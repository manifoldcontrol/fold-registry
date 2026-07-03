"""
csr_extract.py — extract source-document prose for registry entries.

Given a CSR locator like
    csr.document.MyDoc@v1.0#section.3.2.my_symbol
this module finds the source LaTeX file for `csr.document.MyDoc`, walks its
section tree to find §3.2, extracts that section's text, and converts a useful
subset of LaTeX to HTML.

The result is rendered inline in CSR.wiki.html so a registry entry shows both
its metadata and the canonical prose from the source document.
"""

from __future__ import annotations

import html as _html
import re
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import subprocess

# ----------------------------------------------------------------------------
# Source-document path map: registry document ID -> path relative to CSR root
# ----------------------------------------------------------------------------

# Resolved relative to the parent of tools/csr_extract.py, i.e. the csr/ dir.
# Layout: <corpus_root>/<registry_dir>/  (the registry dir sits one level below corpus root).
# corpus_root is the directory two levels above build/ (see csr_config.yaml),
# other framework documents. Walk up one level only.
PF_ROOT_FROM_CSR = Path("..")

SOURCE_PATHS: Dict[str, Path] = {
    # Legacy fallback map. Empty in the seed template.
    # Each document's source_path field in registry/documents.csr is now
    # the authoritative source of truth; this dict is only used when an
    # entry has no declared source_path.
}

LOCATOR_RE = re.compile(
    r"^csr\.document\.(?P<doc>[A-Za-z_][A-Za-z0-9_]*)"
    r"@v(?P<version>[0-9][A-Za-z0-9._-]*)"
    r"#section\.(?P<section>[0-9][0-9.]*)"
    r"\.(?P<anchor>[A-Za-z_][A-Za-z0-9_-]*)$"
)


# ----------------------------------------------------------------------------
# LaTeX section walker
# ----------------------------------------------------------------------------

# Match \section{...}, \subsection{...}, \subsubsection{...}, with or without star.
# Captures: starred (* or empty), level keyword, title text.
SECTION_RE = re.compile(
    r"^\\(?P<level>section|subsection|subsubsection)(?P<star>\*?)\s*\{(?P<title>[^}]*)\}",
    re.MULTILINE,
)

LEVEL_DEPTH = {"section": 1, "subsection": 2, "subsubsection": 3}


def walk_sections(tex: str) -> List[Tuple[str, str, str, int, int]]:
    """Walk a LaTeX file and return a list of
        (section_path, title, body, start_offset, end_offset)
    tuples, where section_path is a dotted numeric like "1", "2.1", "6.5".

    Starred sections (\\section*{...}) participate in numbering when at the
    section level (some source-doc conventions hand-number starred Roman-numeral
    headers via \\section*). For simpler source documents we count both
    starred and unstarred. Resolution: if all top-level sections are starred,
    we still number them; if a mix, we count only unstarred (standard LaTeX rule).
    """
    matches = list(SECTION_RE.finditer(tex))
    if not matches:
        return []

    # Determine numbering policy. LaTeX convention: starred sections are
    # unnumbered. But some source documents hand-number starred
    # sections with Roman numerals in the title. Policy:
    #   - If all top-level (section) entries are unstarred: count only unstarred.
    #   - If all top-level entries are starred: count all of them (Wiki convention).
    #   - If mixed: count only unstarred (the standard LaTeX numbering rule).
    top_level_matches = [m for m in matches if m.group("level") == "section"]
    if not top_level_matches:
        return []
    all_top_starred = all(m.group("star") for m in top_level_matches)
    count_starred_at_section_level = all_top_starred

    counters = [0, 0, 0]  # [section, subsection, subsubsection]
    entries: List[Tuple[str, str, str, int, int]] = []

    for i, m in enumerate(matches):
        level = m.group("level")
        depth = LEVEL_DEPTH[level]
        title = m.group("title").strip()
        starred = bool(m.group("star"))

        # Skip starred sections at section level unless we're using all-starred mode.
        if level == "section" and starred and not count_starred_at_section_level:
            continue
        # At subsection/subsubsection level, skip starred entries from numbering
        # but still preserve them in entries with no numeric path (they may be
        # reached via anchor-based lookup).
        if level != "section" and starred:
            start = m.end()
            end = matches[i + 1].start() if i + 1 < len(matches) else len(tex)
            body = tex[start:end].strip()
            entries.append(("", title, body, start, end))
            continue

        # Bump counter at this depth, reset deeper counters
        counters[depth - 1] += 1
        for d in range(depth, 3):
            counters[d] = 0

        # Build section path "1", "1.2", "1.2.3"
        path_parts = [str(counters[d]) for d in range(depth) if counters[d] > 0]
        path = ".".join(path_parts)

        start = m.end()
        # Body extent: continue until the next heading AT SAME OR SHALLOWER
        # depth. A section's body therefore includes all its subsections, which
        # anchor-based extraction needs to find sub-paragraphs like
        # \subsection*{Axiom 27 ...} embedded inside §10.
        end = len(tex)
        for j in range(i + 1, len(matches)):
            next_depth = LEVEL_DEPTH[matches[j].group("level")]
            if next_depth <= depth:
                end = matches[j].start()
                break
        body = tex[start:end].strip()

        entries.append((path, title, body, start, end))

    return entries


# ----------------------------------------------------------------------------
# Anchor-based extraction (for axioms inside a section)
# ----------------------------------------------------------------------------

def extract_anchored_paragraph(body: str, anchor: str) -> Optional[str]:
    """Look for the anchor within a section body. Used for axiom_9, axiom_27, etc.
    where the locator section is the containing section but the actual content is
    a smaller paragraph identified by anchor.
    Returns the paragraph(s) starting at the anchor, ending at the next
    \\subsection*{...} or \\section{...} boundary."""

    # Heuristic: if anchor looks like axiom_N, look for `\subsection*{Axiom N` etc.
    m_axiom = re.match(r"axiom_(\d+)", anchor)
    if m_axiom:
        n = m_axiom.group(1)
        # Look for \subsection*{Axiom N. ...}
        ax_re = re.compile(
            rf"\\subsection\*\{{Axiom\s+{n}[\.\s]",
            re.IGNORECASE,
        )
        match = ax_re.search(body)
        if match:
            start = match.start()
            # End at next \subsection*{ or \section{ or end of body
            end_re = re.compile(r"\\(subsection|section)\*?\s*\{", re.MULTILINE)
            end_match = None
            for em in end_re.finditer(body, pos=match.end()):
                end_match = em
                break
            end = end_match.start() if end_match else len(body)
            return body[start:end].strip()

    # Generic: try to find a paragraph header containing the anchor word
    anchor_words = anchor.replace("_", " ").lower()
    for line_match in re.finditer(r"\\subsection\*?\s*\{([^}]*)\}", body):
        if anchor_words in line_match.group(1).lower():
            start = line_match.start()
            # Find next subsection break
            end_re = re.compile(r"\\(subsection|section)\*?\s*\{", re.MULTILINE)
            next_match = None
            for em in end_re.finditer(body, pos=line_match.end()):
                next_match = em
                break
            end = next_match.start() if next_match else len(body)
            return body[start:end].strip()

    return None


# ----------------------------------------------------------------------------
# Basic LaTeX -> HTML conversion
# ----------------------------------------------------------------------------

# Order matters: process commands before stripping braces.
LATEX_HTML_RULES: List[Tuple[re.Pattern, str]] = [
    # Strip comments (but preserve \% which is escaped percent)
    (re.compile(r"(?<!\\)%[^\n]*"), ""),
    # Normalize tilde non-breaking space and ~~ formatting
    (re.compile(r"~~"), " "),
    (re.compile(r"~"), " "),
    # \textbf{...}, \textit{...}, \emph{...}, \texttt{...}
    (re.compile(r"\\textbf\{([^{}]+)\}"), r"<strong>\1</strong>"),
    (re.compile(r"\\textit\{([^{}]+)\}"), r"<em>\1</em>"),
    (re.compile(r"\\emph\{([^{}]+)\}"), r"<em>\1</em>"),
    (re.compile(r"\\texttt\{([^{}]+)\}"), r"<code>\1</code>"),
    # \mathcal{X} -> X (with class hint)
    (re.compile(r"\\mathcal\{([^{}]+)\}"), r"<span class='math-cal'>\1</span>"),
    (re.compile(r"\\mathbb\{([^{}]+)\}"), r"<span class='math-bb'>\1</span>"),
    (re.compile(r"\\mathrm\{([^{}]+)\}"), r"\1"),
    # Cross-ref / label: drop
    (re.compile(r"\\label\{[^{}]*\}"), ""),
    (re.compile(r"\\ref\{[^{}]*\}"), "[ref]"),
    (re.compile(r"\\eqref\{[^{}]*\}"), "[eq]"),
    (re.compile(r"\\cite\{[^{}]*\}"), "[cite]"),
    # Greek letters and common symbols
    (re.compile(r"\\alpha\b"),    "α"),
    (re.compile(r"\\beta\b"),     "β"),
    (re.compile(r"\\gamma\b"),    "γ"),
    (re.compile(r"\\delta\b"),    "δ"),
    (re.compile(r"\\epsilon\b"),  "ε"),
    (re.compile(r"\\varepsilon\b"), "ε"),
    (re.compile(r"\\theta\b"),    "θ"),
    (re.compile(r"\\lambda\b"),   "λ"),
    (re.compile(r"\\mu\b"),       "μ"),
    (re.compile(r"\\nu\b"),       "ν"),
    (re.compile(r"\\pi\b"),       "π"),
    (re.compile(r"\\rho\b"),      "ρ"),
    (re.compile(r"\\sigma\b"),    "σ"),
    (re.compile(r"\\tau\b"),      "τ"),
    (re.compile(r"\\phi\b"),      "φ"),
    (re.compile(r"\\varphi\b"),   "φ"),
    (re.compile(r"\\psi\b"),      "ψ"),
    (re.compile(r"\\omega\b"),    "ω"),
    (re.compile(r"\\Gamma\b"),    "Γ"),
    (re.compile(r"\\Delta\b"),    "Δ"),
    (re.compile(r"\\Theta\b"),    "Θ"),
    (re.compile(r"\\Lambda\b"),   "Λ"),
    (re.compile(r"\\Sigma\b"),    "Σ"),
    (re.compile(r"\\Phi\b"),      "Φ"),
    (re.compile(r"\\Omega\b"),    "Ω"),
    (re.compile(r"\\to\b"),       "→"),
    (re.compile(r"\\rightarrow\b"), "→"),
    (re.compile(r"\\leftarrow\b"),  "←"),
    (re.compile(r"\\leftrightarrow\b"), "↔"),
    (re.compile(r"\\Rightarrow\b"), "⇒"),
    (re.compile(r"\\implies\b"),  "⇒"),
    (re.compile(r"\\iff\b"),      "⇔"),
    (re.compile(r"\\subseteq\b"), "⊆"),
    (re.compile(r"\\subset\b"),   "⊂"),
    (re.compile(r"\\supseteq\b"), "⊇"),
    (re.compile(r"\\in\b"),       "∈"),
    (re.compile(r"\\notin\b"),    "∉"),
    (re.compile(r"\\geq\b"),      "≥"),
    (re.compile(r"\\leq\b"),      "≤"),
    (re.compile(r"\\neq\b"),      "≠"),
    (re.compile(r"\\equiv\b"),    "≡"),
    (re.compile(r"\\circ\b"),     "∘"),
    (re.compile(r"\\cdot\b"),     "·"),
    (re.compile(r"\\times\b"),    "×"),
    (re.compile(r"\\infty\b"),    "∞"),
    (re.compile(r"\\partial\b"),  "∂"),
    (re.compile(r"\\nabla\b"),    "∇"),
    (re.compile(r"\\sum\b"),      "∑"),
    (re.compile(r"\\prod\b"),     "∏"),
    (re.compile(r"\\int\b"),      "∫"),
    (re.compile(r"\\forall\b"),   "∀"),
    (re.compile(r"\\exists\b"),   "∃"),
    (re.compile(r"\\emptyset\b"), "∅"),
    (re.compile(r"\\langle\b"),   "⟨"),
    (re.compile(r"\\rangle\b"),   "⟩"),
    # Subscript/superscript: best effort for single-char
    (re.compile(r"_\{([^{}]+)\}"), r"<sub>\1</sub>"),
    (re.compile(r"\^\{([^{}]+)\}"), r"<sup>\1</sup>"),
    (re.compile(r"_([A-Za-z0-9])"), r"<sub>\1</sub>"),
    (re.compile(r"\^([A-Za-z0-9])"), r"<sup>\1</sup>"),
    # \\ line break
    (re.compile(r"\\\\\s*"), "<br>"),
    # \% -> %
    (re.compile(r"\\%"), "%"),
    # \& -> &amp; (we'll re-escape later, so keep as &)
    (re.compile(r"\\&"), "&"),
    # \$ -> $
    (re.compile(r"\\\$"), "$"),
    # \# -> #
    (re.compile(r"\\#"), "#"),
    # \_ -> _
    (re.compile(r"\\_"), "_"),
    # \{ \} -> { }
    (re.compile(r"\\\{"), "{"),
    (re.compile(r"\\\}"), "}"),
    # Strip remaining \command{arg} keeping arg
    (re.compile(r"\\(?:paragraph|subparagraph)\*?\s*\{([^{}]+)\}"),
     r"<strong>\1.</strong>"),
]

ENV_RULES: List[Tuple[re.Pattern, str]] = [
    # itemize / enumerate
    (re.compile(r"\\begin\{itemize\}(?:\[[^\]]*\])?", re.DOTALL), "<ul>"),
    (re.compile(r"\\end\{itemize\}"), "</ul>"),
    (re.compile(r"\\begin\{enumerate\}(?:\[[^\]]*\])?", re.DOTALL), "<ol>"),
    (re.compile(r"\\end\{enumerate\}"), "</ol>"),
    # \item -> <li>
    (re.compile(r"\\item\s+"), "<li>"),
    # quote / quotation
    (re.compile(r"\\begin\{quote\}"), "<blockquote>"),
    (re.compile(r"\\end\{quote\}"), "</blockquote>"),
    # center -> div centered
    (re.compile(r"\\begin\{center\}"), '<div style="text-align:center">'),
    (re.compile(r"\\end\{center\}"), "</div>"),
    # tabular - too complex; replace with placeholder
    (re.compile(r"\\begin\{tabular\}.*?\\end\{tabular\}", re.DOTALL),
     "<em>[table omitted from extracted view; see source PDF]</em>"),
    # equation / equation* / align - keep as preformatted math
    (re.compile(r"\\begin\{(equation|equation\*|align|align\*|displaymath)\}(.*?)\\end\{\1\}", re.DOTALL),
     r'<pre class="math-display">\2</pre>'),
    # figure / table floats - placeholder
    (re.compile(r"\\begin\{figure\}.*?\\end\{figure\}", re.DOTALL),
     "<em>[figure omitted from extracted view]</em>"),
    # itemize without proper close (defensive)
]




# ----------------------------------------------------------------------------
# LaTeX math → Unicode HTML (server-side rendering, no JS dependency)
# ----------------------------------------------------------------------------

# Greek letters
_GREEK = {
    "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε",
    "varepsilon": "ε", "zeta": "ζ", "eta": "η", "theta": "θ", "vartheta": "ϑ",
    "iota": "ι", "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν",
    "xi": "ξ", "pi": "π", "varpi": "ϖ", "rho": "ρ", "varrho": "ϱ",
    "sigma": "σ", "varsigma": "ς", "tau": "τ", "upsilon": "υ", "phi": "φ",
    "varphi": "φ", "chi": "χ", "psi": "ψ", "omega": "ω",
    "Alpha": "Α", "Beta": "Β", "Gamma": "Γ", "Delta": "Δ", "Epsilon": "Ε",
    "Zeta": "Ζ", "Eta": "Η", "Theta": "Θ", "Iota": "Ι", "Kappa": "Κ",
    "Lambda": "Λ", "Mu": "Μ", "Nu": "Ν", "Xi": "Ξ", "Pi": "Π",
    "Rho": "Ρ", "Sigma": "Σ", "Tau": "Τ", "Upsilon": "Υ", "Phi": "Φ",
    "Chi": "Χ", "Psi": "Ψ", "Omega": "Ω",
}

# Math operators and symbols
_OPS = {
    "to": "→", "rightarrow": "→", "Rightarrow": "⇒", "leftarrow": "←",
    "leftrightarrow": "↔", "Leftrightarrow": "⇔", "iff": "⇔",
    "implies": "⇒", "mapsto": "↦",
    "le": "≤", "leq": "≤", "ge": "≥", "geq": "≥", "ne": "≠", "neq": "≠",
    "equiv": "≡", "approx": "≈", "sim": "∼", "simeq": "≃",
    "subset": "⊂", "subseteq": "⊆", "supset": "⊃", "supseteq": "⊇",
    "in": "∈", "notin": "∉", "ni": "∋", "cap": "∩", "cup": "∪",
    "emptyset": "∅", "varnothing": "∅",
    "forall": "∀", "exists": "∃", "nexists": "∄",
    "neg": "¬", "lnot": "¬", "land": "∧", "lor": "∨", "wedge": "∧", "vee": "∨",
    "cdot": "·", "times": "×", "div": "÷", "pm": "±", "mp": "∓",
    "circ": "∘", "bullet": "•", "ast": "∗", "star": "⋆", "oplus": "⊕",
    "otimes": "⊗", "odot": "⊙",
    "infty": "∞", "partial": "∂", "nabla": "∇",
    "sum": "∑", "prod": "∏", "int": "∫", "iint": "∬", "oint": "∮",
    "langle": "⟨", "rangle": "⟩", "lceil": "⌈", "rceil": "⌉",
    "lfloor": "⌊", "rfloor": "⌋",
    "leftarrow": "←", "Leftarrow": "⇐",
    "perp": "⊥", "parallel": "∥",
    "ldots": "…", "cdots": "⋯", "vdots": "⋮", "ddots": "⋱",
    "prime": "′", "ell": "ℓ",
    "hat": "̂", "tilde": "̃", "bar": "̄", "vec": "→",
    "mathbb": None,  # special: handled separately
    "mathcal": None, "mathfrak": None, "mathrm": None, "mathit": None,
    "mathsf": None, "mathbf": None, "mathtt": None, "boldsymbol": None,
}

# Mathcal mapping (Unicode mathematical script letters)
_MATHCAL = {
    "A": "𝒜", "B": "ℬ", "C": "𝒞", "D": "𝒟", "E": "ℰ", "F": "ℱ",
    "G": "𝒢", "H": "ℋ", "I": "ℐ", "J": "𝒥", "K": "𝒦", "L": "ℒ",
    "M": "ℳ", "N": "𝒩", "O": "𝒪", "P": "𝒫", "Q": "𝒬", "R": "ℛ",
    "S": "𝒮", "T": "𝒯", "U": "𝒰", "V": "𝒱", "W": "𝒲", "X": "𝒳",
    "Y": "𝒴", "Z": "𝒵",
}

# Mathbb mapping (Unicode mathematical double-struck letters)
_MATHBB = {
    "A": "𝔸", "B": "𝔹", "C": "ℂ", "D": "𝔻", "E": "𝔼", "F": "𝔽",
    "G": "𝔾", "H": "ℍ", "I": "𝕀", "J": "𝕁", "K": "𝕂", "L": "𝕃",
    "M": "𝕄", "N": "ℕ", "O": "𝕆", "P": "ℙ", "Q": "ℚ", "R": "ℝ",
    "S": "𝕊", "T": "𝕋", "U": "𝕌", "V": "𝕍", "W": "𝕎", "X": "𝕏",
    "Y": "𝕐", "Z": "ℤ",
}

# Mathfrak mapping (Unicode mathematical Fraktur)
_MATHFRAK = {
    "A": "𝔄", "B": "𝔅", "C": "ℭ", "D": "𝔇", "E": "𝔈", "F": "𝔉",
    "G": "𝔊", "H": "ℌ", "I": "ℑ", "J": "𝔍", "K": "𝔎", "L": "𝔏",
    "M": "𝔐", "N": "𝔑", "O": "𝔒", "P": "𝔓", "Q": "𝔔", "R": "ℜ",
    "S": "𝔖", "T": "𝔗", "U": "𝔘", "V": "𝔙", "W": "𝔚", "X": "𝔛",
    "Y": "𝔜", "Z": "ℨ",
}

# Subscript / superscript Unicode (digits + a few letters that have them)
_SUB_DIGITS = "₀₁₂₃₄₅₆₇₈₉"
_SUP_DIGITS = "⁰¹²³⁴⁵⁶⁷⁸⁹"
_SUB_LETTERS = {"a":"ₐ","e":"ₑ","h":"ₕ","i":"ᵢ","j":"ⱼ","k":"ₖ","l":"ₗ","m":"ₘ",
                "n":"ₙ","o":"ₒ","p":"ₚ","r":"ᵣ","s":"ₛ","t":"ₜ","u":"ᵤ","v":"ᵥ","x":"ₓ",
                "+": "₊", "-": "₋", "=": "₌", "(": "₍", ")": "₎"}
_SUP_LETTERS = {"a":"ᵃ","b":"ᵇ","c":"ᶜ","d":"ᵈ","e":"ᵉ","f":"ᶠ","g":"ᵍ","h":"ʰ",
                "i":"ⁱ","j":"ʲ","k":"ᵏ","l":"ˡ","m":"ᵐ","n":"ⁿ","o":"ᵒ","p":"ᵖ",
                "r":"ʳ","s":"ˢ","t":"ᵗ","u":"ᵘ","v":"ᵛ","w":"ʷ","x":"ˣ","y":"ʸ","z":"ᶻ",
                "+": "⁺", "-": "⁻", "=": "⁼", "(": "⁽", ")": "⁾"}


def _to_subscript(s: str) -> str:
    """Try to render s as Unicode subscripts. Falls back to <sub>.</sub> for
    characters with no Unicode subscript form."""
    out = []
    fallback = False
    for ch in s:
        if ch.isdigit():
            out.append(_SUB_DIGITS[int(ch)])
        elif ch in _SUB_LETTERS:
            out.append(_SUB_LETTERS[ch])
        elif ch == " ":
            out.append(" ")
        else:
            fallback = True
            break
    if fallback:
        return "<sub>" + s + "</sub>"
    return "".join(out)


def _to_superscript(s: str) -> str:
    out = []
    fallback = False
    for ch in s:
        if ch.isdigit():
            out.append(_SUP_DIGITS[int(ch)])
        elif ch in _SUP_LETTERS:
            out.append(_SUP_LETTERS[ch])
        elif ch == " ":
            out.append(" ")
        else:
            fallback = True
            break
    if fallback:
        return "<sup>" + s + "</sup>"
    return "".join(out)


def latex_math_to_unicode(latex: str) -> str:
    """Convert a LaTeX math expression to readable HTML using Unicode where
    possible, falling back to <sub>/<sup>/<em> for unsupported constructs.
    Lossy but readable. Returns inner HTML (no surrounding span)."""
    s = latex

    # Spacing commands first (before subscript / Greek to avoid mid-stream confusion)
    s = re.sub(r"\\,", " ", s)
    s = re.sub(r"\\;", " ", s)
    s = re.sub(r"\\:", " ", s)
    s = re.sub(r"\\!", "", s)
    s = re.sub(r"\\quad\b", "  ", s)
    s = re.sub(r"\\qquad\b", "    ", s)

    # Accents: combining-diacritic Unicode for one-letter targets, fallback prefix otherwise.
    _ACCENTS = {
        "dot":   "̇",  # combining dot above
        "ddot":  "̈",  # combining diaeresis
        "hat":   "̂",  # combining circumflex
        "tilde": "̃",  # combining tilde
        "bar":   "̄",  # combining macron
        "vec":   "⃗",  # combining right arrow above
        "check": "̌",  # combining caron
        "breve": "̆",  # combining breve
        "acute": "́",  # combining acute
        "grave": "̀",  # combining grave
    }
    for cmd, diacritic in _ACCENTS.items():
        # \dot{X} -> X + diacritic (multi-char content gets diacritic on first char)
        def _make_repl(d):
            def _repl(m):
                body = m.group(1)
                if not body:
                    return body
                return body[0] + d + body[1:]
            return _repl
        s = re.sub(r"\\" + cmd + r"\s*\{([^{}]+)\}", _make_repl(diacritic), s)
        # \dot X (no braces) form
        s = re.sub(r"\\" + cmd + r"\s+([A-Za-z])",
                   lambda m, d=diacritic: m.group(1) + d, s)


    # \mathcal{X} -> Unicode script
    def _mathcal_repl(m):
        body = m.group(1)
        return "".join(_MATHCAL.get(c, c) for c in body)
    s = re.sub(r"\\mathcal\s*\{([^{}]+)\}", _mathcal_repl, s)

    # \mathbb{X} -> Unicode double-struck
    def _mathbb_repl(m):
        body = m.group(1)
        return "".join(_MATHBB.get(c, c) for c in body)
    s = re.sub(r"\\mathbb\s*\{([^{}]+)\}", _mathbb_repl, s)

    # \mathfrak{X} -> Fraktur
    def _frak_repl(m):
        body = m.group(1)
        return "".join(_MATHFRAK.get(c, c) for c in body)
    s = re.sub(r"\\mathfrak\s*\{([^{}]+)\}", _frak_repl, s)

    # \mathrm{xxx}, \operatorname, \text -> upright / plain
    s = re.sub(r"\\mathrm\s*\{([^{}]+)\}", r"\1", s)
    s = re.sub(r"\\operatorname\s*\{([^{}]+)\}", r"\1", s)
    s = re.sub(r"\\text\s*\{([^{}]+)\}", r"\1", s)
    s = re.sub(r"\\textsf\s*\{([^{}]+)\}", r"\1", s)
    s = re.sub(r"\\mathit\s*\{([^{}]+)\}", r"<em>\1</em>", s)
    s = re.sub(r"\\mathbf\s*\{([^{}]+)\}", r"<strong>\1</strong>", s)
    s = re.sub(r"\\boldsymbol\s*\{([^{}]+)\}", r"<strong>\1</strong>", s)

    # \frac{a}{b} -> a/b
    s = re.sub(r"\\frac\s*\{([^{}]+)\}\s*\{([^{}]+)\}", r"(\1)/(\2)", s)
    # \sqrt{x} -> √x
    s = re.sub(r"\\sqrt\s*\{([^{}]+)\}", r"√(\1)", s)

    # Greek letters and operator symbols. Each name is matched as
    # \<name> followed by a non-letter boundary. Use a single backslash in the
    # regex, since the input has a single backslash for LaTeX commands.
    for name, sym in _GREEK.items():
        s = re.sub(r"\\" + name + r"(?![A-Za-z])", sym, s)
    for name, sym in _OPS.items():
        if sym is None:
            continue
        s = re.sub(r"\\" + name + r"(?![A-Za-z])", sym, s)

    # Subscripts: _{...} and _X
    s = re.sub(r"_\s*\{([^{}]+)\}",
               lambda m: _to_subscript(m.group(1)), s)
    s = re.sub(r"_([A-Za-z0-9])",
               lambda m: _to_subscript(m.group(1)), s)
    # Superscripts: ^{...} and ^X
    s = re.sub(r"\^\s*\{([^{}]+)\}",
               lambda m: _to_superscript(m.group(1)), s)
    s = re.sub(r"\^([A-Za-z0-9])",
               lambda m: _to_superscript(m.group(1)), s)

    # Strip remaining \command{arg} keeping the argument
    s = re.sub(r"\\([a-zA-Z]+)\*?\s*\{([^{}]*)\}", r"\2", s)
    # Strip remaining \command tokens with no args
    s = re.sub(r"\\([a-zA-Z]+)\*?", "", s)

    # Collapse whitespace
    s = re.sub(r"\s+", " ", s).strip()

    return s





_LATEX_TO_HTML_CACHE: Dict[str, str] = {}


def latex_to_html(text: str) -> str:
    r"""Convert a LaTeX section body to HTML via pandoc.

    Pandoc handles theorem-like environments, accents, escapes, math, tables,
    cross-refs - the things hand-rolled regex pipelines cannot complete.
    Math is emitted in MathJax / KaTeX delimiters \(...\) inline and
    \[...\] display, which the rendered HTML view picks up via KaTeX
    auto-render.

    Falls back to a minimal regex pass if pandoc is unavailable, so the
    extractor degrades gracefully instead of failing the whole build.

    Memoised by input text: hundreds of registry entries that resolve to the
    same wiki section share a body string and need only one pandoc call.
    """
    if not text or not text.strip():
        return ""
    cached = _LATEX_TO_HTML_CACHE.get(text)
    if cached is not None:
        return cached

    # Wrap in minimal preamble that defines commonly-used framework custom
    # commands as no-ops or theorem environments. Pandoc requires environments
    # to be declared; otherwise it complains about "principle" etc.
    preamble = r"""
\newtheorem{principle}{Principle}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{corollary}{Corollary}
\newtheorem{definition}{Definition}
\newtheorem{proposition}{Proposition}
\newtheorem{conjecture}{Conjecture}
\newtheorem{claim}{Claim}
\newtheorem{remark}{Remark}
\newtheorem{observation}{Observation}
\newtheorem{note}{Note}
\newcommand{\sffamily}{}
\newcommand{\rmfamily}{}
\newcommand{\bfseries}{}
\newcommand{\itshape}{}
\newcommand{\large}{}
\newcommand{\small}{}
\newcommand{\noindent}{}
"""
    wrapped = preamble + "\n\\begin{document}\n" + text + "\n\\end{document}\n"

    try:
        result = subprocess.run(
            ["pandoc", "-f", "latex", "-t", "html5", "--mathjax",
             "--wrap=preserve", "--no-highlight"],
            input=wrapped,
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            timeout=15,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
        # Pandoc unavailable or hung — degrade to a minimal regex pass that
        # at least strips the most common LaTeX commands.
        fb = _fallback_latex_to_html(text)
        _LATEX_TO_HTML_CACHE[text] = fb
        return fb

    if result.returncode != 0:
        # Pandoc failed; fall back rather than failing the whole build.
        fb = _fallback_latex_to_html(text)
        _LATEX_TO_HTML_CACHE[text] = fb
        return fb

    html = result.stdout.strip()
    _LATEX_TO_HTML_CACHE[text] = html
    return html


def _fallback_latex_to_html(text: str) -> str:
    """Minimal fallback when pandoc is unavailable. Strips common LaTeX
    formatting and preserves math-mode regions verbatim for client-side
    rendering. Lossy but readable."""
    s = text
    # Comments
    s = re.sub(r"(?<!\\)%[^\n]*", "", s)
    # Tildes
    s = re.sub(r"~+", " ", s)
    # \textbf, \textit, \emph, \texttt
    s = re.sub(r"\\textbf\{([^{}]+)\}", r"<strong>\1</strong>", s)
    s = re.sub(r"\\(textit|emph)\{([^{}]+)\}", r"<em>\2</em>", s)
    s = re.sub(r"\\texttt\{([^{}]+)\}", r"<code>\1</code>", s)
    # \\ -> <br>
    s = re.sub(r"\\\\\s*", "<br>", s)
    # \_, \&, \#, \%, \$
    s = s.replace("\\_", "_").replace("\\&", "&amp;").replace("\\#", "#")
    s = s.replace("\\%", "%").replace("\\$", "$")
    # Strip remaining \command{arg} -> arg
    s = re.sub(r"\\([a-zA-Z]+)\*?\s*\{([^{}]*)\}", r"\2", s)
    # Strip remaining \command tokens
    s = re.sub(r"\\[a-zA-Z]+\*?", "", s)
    # Paragraph splitting on blank lines
    paras = [p.strip() for p in re.split(r"\n\s*\n", s) if p.strip()]
    return "\n\n".join("<p>" + p + "</p>" for p in paras)



# ----------------------------------------------------------------------------
# Public API
# ----------------------------------------------------------------------------

class SourceCache:
    """Cache parsed source documents to avoid re-walking on every symbol."""
    def __init__(self, csr_root: Path):
        self.csr_root = csr_root
        self._docs: Dict[str, Optional[List[Tuple[str, str, str, int, int]]]] = {}
        self._raw: Dict[str, str] = {}
        # Cache pandoc output keyed by (doc_id, section_path, anchor) so
        # multi-hundred-symbol batches don't re-spawn pandoc per locator.
        self._html_cache: Dict[Tuple[str, str, str], Optional[str]] = {}

    def _resolve(self, doc_id: str) -> Optional[Path]:
        rel = SOURCE_PATHS.get(doc_id)
        if rel is None:
            return None
        return (self.csr_root / PF_ROOT_FROM_CSR / rel).resolve()

    def get_sections(self, doc_id: str) -> Optional[List[Tuple[str, str, str, int, int]]]:
        if doc_id in self._docs:
            return self._docs[doc_id]
        path = self._resolve(doc_id)
        if path is None or not path.exists():
            self._docs[doc_id] = None
            return None
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            self._docs[doc_id] = None
            return None
        self._raw[doc_id] = text
        if path.suffix == ".tex":
            self._docs[doc_id] = walk_sections(text)
        else:
            # For .md / .lean we don't parse sections; just hold raw
            self._docs[doc_id] = []
        return self._docs[doc_id]




def clean_section_title(title):
    """Strip LaTeX styling commands and normalize whitespace in a section title.
    Used by extract_for_locator before the title is rendered into the
    source-header label."""
    if not title:
        return ""
    s = title
    # Handle backslash-escaped specials BEFORE stripping leftover commands
    s = s.replace("\\_", "_")
    s = s.replace("\\&", "&")
    s = s.replace("\\#", "#")
    s = s.replace("\\%", "%")
    s = s.replace("\\$", "$")
    # Drop font/size styling commands: \sffamily, \large, \bfseries, etc.
    s = re.sub(r"\\(sffamily|rmfamily|ttfamily|bfseries|itshape|small|large|huge|tiny|footnotesize|normalsize|scriptsize)\b", "", s)
    # Strip remaining \command tokens
    s = re.sub(r"\\[a-zA-Z]+\*?", "", s)
    # ~~ and ~ to space
    s = re.sub(r"~+", " ", s)
    # Drop curly braces
    s = re.sub(r"[{}]", "", s)
    # Collapse whitespace
    s = re.sub(r"\s+", " ", s).strip()
    return s

def extract_for_locator(cache: SourceCache, locator: str,
                         max_chars: int = 4000) -> Optional[str]:
    """Given a CSR locator, return the source-document prose for that section
    converted to HTML. Returns None if the locator is unparseable or the source
    document is unavailable."""
    m = LOCATOR_RE.match(locator.strip())
    if not m:
        return None

    doc_short = m.group("doc")
    doc_id = "csr.document." + doc_short
    target_section = m.group("section")
    anchor = m.group("anchor")

    # Skip self-referential extraction: the snapshot view IS the wiki view,
    # so embedding wiki prose into wiki-anchored entries is circular and
    # makes the snapshot render quadratic in the number of wiki entries.
    # Configurable self-reference skip: a registered document can be marked
    # as a wiki-snapshot view; embedding its own prose into itself is circular.
    # Set the SELF_REFERENTIAL_DOC_SHORTS list below per project.
    if doc_short in SELF_REFERENTIAL_DOC_SHORTS:
        return None

    # Memoise the rendered HTML by (doc, section, anchor); pandoc invocations
    # are by far the dominant cost when extracting hundreds of locators.
    cache_key = (doc_id, target_section, anchor)
    if cache_key in cache._html_cache:
        return cache._html_cache[cache_key]

    sections = cache.get_sections(doc_id)
    if not sections:
        cache._html_cache[cache_key] = None
        return None

    # First try exact section match
    matched = None
    for path, title, body, _, _ in sections:
        if path == target_section:
            matched = (path, title, body)
            break
    if matched is None:
        # Try anchor-based lookup within sections at the target depth
        target_depth = target_section.count(".") + 1
        for path, title, body, _, _ in sections:
            if not path:
                continue
            depth = path.count(".") + 1
            if depth == target_depth and anchor.lower() in title.lower().replace(" ", "_"):
                matched = (path, title, body)
                break

    if matched is None:
        cache._html_cache[cache_key] = None
        return None

    path, title, body = matched

    # Try anchor-based paragraph extraction within the section body
    para = extract_anchored_paragraph(body, anchor)
    if para:
        body = para

    # Trim to max_chars
    if len(body) > max_chars:
        body = body[:max_chars] + "\n\n[... truncated; see source for full text]"

    html = latex_to_html(body)

    rendered = f'<div class="source-prose"><div class="source-header">Source: §{path} {_html.escape(clean_section_title(title))}</div>\n{html}\n</div>'
    cache._html_cache[cache_key] = rendered
    return rendered


# ----------------------------------------------------------------------------
# CLI smoke test
# ----------------------------------------------------------------------------

if __name__ == "__main__":
    import sys
    if len(sys.argv) < 2:
        print("usage: csr_extract.py <locator>")
        sys.exit(1)
    here = Path(__file__).resolve().parent.parent
    cache = SourceCache(here)
    result = extract_for_locator(cache, sys.argv[1])
    if result is None:
        print("no extraction")
    else:
        print(result)

"""
csr_compile.py - Phase 1A compiler for the Corpus Semantic Registry (CSR v0.1.1).

Pipeline (§22 of CSR_v0.1.1_Spec):
  1.  preprocess (autolink sanitation per §B.15)
  2.  parse declarations
  3.  lower to typed AST
  4.  validate schema
  5.  resolve imports
  6.  normalize IDs
  7.  resolve aliases
  8.  derive inverse relations (§B.10)
  9.  compute definition hashes (three-layer per §C.6)
  10. build typed relation graph
  11. validate invariants
  12. apply relation cardinality rules
  13. apply cycle policy
  14. (deferred to Phase 1C) compare against prior lockfile and classify drift
  15. (deferred to Phase 1C) enforce drift action policy
  16. (deferred to Phase 1C) validate promotion-rule legality on status changes
  17. emit lockfile
  18. (deferred to Phase 1D) render reference outputs

Phase 1A scope ends at lockfile emission and a validation report. Diagnostic codes
CSR001-CSR020 are wired inline through validation passes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from dataclasses import dataclass, field, asdict, is_dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

try:
    import csr_extract  # type: ignore
except ImportError:
    csr_extract = None

# ----------------------------------------------------------------------------
# Constants and enums (closed per §6, §7, §B)
# ----------------------------------------------------------------------------

STATUS_ENUM = {
    "draft", "candidate", "provisional", "canonical",
    "deprecated", "rejected", "deferred",
}

VERIFICATION_STATE_ENUM = {
    "declared", "argued", "tested", "formalized", "proved",
}

VERIFICATION_METHOD_ENUM = {
    "prose", "empirical", "theorem", "simulation", "Lean", "compiler_check",
}

SEVERITY_ENUM = {"info", "warn", "error"}

FRAMEWORK_LAYER_ENUM = {
    "procedure", "algebra", "representation", "domain", "cross_layer", "registry",
}

DRIFT_ACTION_ENUM = {
    "accept_new_hash", "create_successor_id", "mark_collision", "deprecate_old",
}

RESOLUTION_ENUM = {
    "pending", "merge", "split", "alias", "reject",
    "subset_with_added_structure", "containment", "quotient",
    "full_supersession",
}

ENTRY_TYPE_ENUM = {
    "symbol", "document", "collision", "invariant",
    "promotion_rule", "migration",
}

# Relation policy table (§B.11 / §15)
RELATION_TYPES = [
    "depends_on", "refines", "instantiates", "used_by",
    "conflicts_with", "equivalent_to", "contains", "component_of",
    "xref_only",
]

# Cycle policy (§B.11)
CYCLE_ERROR_RELATIONS = {"depends_on", "refines", "instantiates", "contains"}
CYCLE_ALLOWED_RELATIONS = {
    "used_by", "equivalent_to", "conflicts_with", "xref_only",
    "supersedes", "superseded_by", "component_of",
}

# Inverse pairs (§B.10)
INVERSE_PAIRS = {
    "contains": "component_of",
    "component_of": "contains",
    "supersedes": "superseded_by",
    "superseded_by": "supersedes",
}
SYMMETRIC_RELATIONS = {"equivalent_to", "conflicts_with", "composes_with"}

# Relation target type rules (§C.7)
RELATION_TARGET_TYPES: Dict[str, Set[str]] = {
    "depends_on":     {"symbol", "document"},
    "refines":        {"symbol"},
    "instantiates":   {"symbol"},
    "used_by":        {"symbol", "document"},
    "conflicts_with": {"symbol", "collision"},
    "equivalent_to":  {"symbol"},
    "contains":       {"symbol"},
    "component_of":   {"symbol"},
    "composes_with":  {"symbol", "document"},
    "xref_only":      {"symbol", "document", "collision", "invariant"},
}

# Status-of-target dependency rules (§C.8)
TARGET_STATUS_DEPENDS_ON: Dict[str, str] = {
    "canonical":   "allow",
    "provisional": "allow",
    "candidate":   "allow",
    "draft":       "warn",
    "deprecated":  "warn_unless_successor",
    "rejected":    "error",
    "deferred":    "error",
}

# Diagnostic codes (§23 / §B body)
DIAG_CODES = {
    "CSR001": "duplicate_symbol_id",
    "CSR002": "unresolved_alias",
    "CSR003": "unresolved_dependency",
    "CSR004": "hash_drift",
    "CSR005": "undeclared_collision",
    "CSR006": "invalid_status",
    "CSR007": "canonical_without_verification",
    "CSR008": "dependency_cycle",
    "CSR009": "invalid_relation_cardinality",
    "CSR010": "missing_source_anchor",
    "CSR011": "invalid_verification_state",
    "CSR012": "invalid_relation_target",
    "CSR013": "import_resolution_failure",
    "CSR014": "drift_action_violates_severity_policy",
    "CSR015": "alias_cycle",
    "CSR016": "illegal_status_promotion",
    "CSR017": "namespace_layer_conflation",
    "CSR018": "inverse_relation_inconsistency",
    "CSR019": "autolink_sanitation_required",
    "CSR020": "source_anchor_corpus_hash_missing",
    "CSR021": "doc_source_unresolvable",
    "CSR023": "doc_source_not_declared",
    "CSR025": "prose_version_embed",
    "CSR026": "symbol_block_truncation_check",
    "CSR027": "notation_collision_check",
}

# CSR027 notation collision (§F.3): plain-capital Latin letters reserved by
# corpus convention. A symbol claiming one of these in symbols_used without
# convention_adapted / aesthetic_override raises a warning.
NOTATION_RESERVED_PLAIN_CAPITALS = {"A", "V", "G", "O", "F", "K", "L"}
NOTATION_PROTECTED_CONVENTION_STATUSES = {
    "convention_adapted", "aesthetic_override",
}
NOTATION_CONVENTION_STATUSES = {
    "convention_aligned", "convention_adapted", "framework_original",
    "aesthetic_override", "divergent_pending_rename",
}

# B.9 locator format: csr.document.<DOC>@v<VERSION>#section.<SECTION>.<ANCHOR>
LOCATOR_RE = re.compile(
    r"^csr\.document\.(?P<doc>[A-Za-z_][A-Za-z0-9_]*)"
    r"@v(?P<version>[0-9][A-Za-z0-9._-]*)"
    # Section: numeric (e.g. 6 or 6.6), numeric+letter (e.g. 5b),
    # or symbolic for framework notes (e.g. preamble, final).
    r"#section\."
    r"(?P<section>(?:[0-9][0-9a-z.]*)|(?:[a-z][a-z0-9_]*))"
    r"\.(?P<anchor>[A-Za-z_][A-Za-z0-9_-]*)$"
)


# ----------------------------------------------------------------------------
# AST node types (§21, §B.17)
# ----------------------------------------------------------------------------

@dataclass
class SourceSpan:
    file: str = ""
    line: int = 0


@dataclass
class SourceAnchor:
    document: str = ""
    version: str = ""
    section: str = ""
    anchor: str = ""
    source_hash: Optional[str] = None
    section_hash: Optional[str] = None
    corpus_hash: Optional[str] = None  # legacy back-compat


@dataclass
class VerificationBlock:
    state: str = "declared"
    method: str = "prose"
    last_verified: str = ""
    evidence: List[SourceAnchor] = field(default_factory=list)


@dataclass
class RelationBlock:
    depends_on:     List[str] = field(default_factory=list)
    refines:        List[str] = field(default_factory=list)
    instantiates:   List[str] = field(default_factory=list)
    used_by:        List[str] = field(default_factory=list)
    conflicts_with: List[str] = field(default_factory=list)
    equivalent_to: List[str] = field(default_factory=list)
    contains:       List[str] = field(default_factory=list)
    component_of:   List[str] = field(default_factory=list)
    composes_with:  List[str] = field(default_factory=list)
    xref_only:      List[str] = field(default_factory=list)


@dataclass
class DriftBlock:
    severity: str = ""
    action: str = ""
    reviewed_by: str = ""
    date: str = ""


@dataclass
class SymbolEntry:
    id: str = ""
    namespace: str = ""
    framework_layer: str = ""
    owning_document: str = ""
    display_name: str = ""
    type: str = "concept"
    status: str = "candidate"
    promotion_target: Optional[str] = None
    applies_to: List[str] = field(default_factory=list)
    definition_home: str = ""
    definition: str = ""
    definition_hash: str = "auto"
    source_anchor: SourceAnchor = field(default_factory=SourceAnchor)
    components: List[str] = field(default_factory=list)
    relations: RelationBlock = field(default_factory=RelationBlock)
    verification: VerificationBlock = field(default_factory=VerificationBlock)
    supersedes: List[str] = field(default_factory=list)
    superseded_by: List[str] = field(default_factory=list)
    drift: Optional[DriftBlock] = None
    notation: Optional[Dict[str, Any]] = None
    source_span: Optional[SourceSpan] = None


@dataclass
class DocumentEntry:
    id: str = ""
    namespace: str = ""
    display_name: str = ""
    version: str = ""
    status: str = "candidate"
    promotion_target: Optional[str] = None
    defines: List[str] = field(default_factory=list)
    depends_on: List[str] = field(default_factory=list)
    publication_mode: str = "internal"
    last_verified: str = ""
    # Optional explicit source path, relative to the corpus root.
    # When present, compute_hashes uses this directly instead of HINTS/FRAMEWORK_MD lookup.
    source_path: Optional[str] = None
    source_span: Optional[SourceSpan] = None


@dataclass
class CollisionEntry:
    id: str = ""
    status: str = "candidate"
    resolution: str = "pending"
    entries: List[str] = field(default_factory=list)
    resolution_note: Optional[str] = None
    resolved_at: Optional[str] = None
    possible_resolutions: List[str] = field(default_factory=list)
    note: Optional[str] = None
    owner: str = ""
    last_verified: str = ""
    source_span: Optional[SourceSpan] = None


@dataclass
class InvariantEntry:
    name: str = ""
    rule: str = ""
    severity: str = "error"
    source_span: Optional[SourceSpan] = None


@dataclass
class PromotionRuleEntry:
    name: str = ""
    requires: List[str] = field(default_factory=list)
    source_span: Optional[SourceSpan] = None


@dataclass
class MigrationEntry:
    name: str = ""
    from_: str = ""
    to: str = ""
    target_wiki_version: str = ""
    status: str = "candidate"
    decision: str = ""
    replaces: List[str] = field(default_factory=list)
    renders: List[str] = field(default_factory=list)
    preserves: List[str] = field(default_factory=list)
    source_span: Optional[SourceSpan] = None


@dataclass
class Alias:
    source: str = ""
    target: str = ""
    source_span: Optional[SourceSpan] = None


@dataclass
class Predecessor:
    source: str = ""
    target: str = ""
    source_span: Optional[SourceSpan] = None


@dataclass
class Import:
    path: str = ""
    source_span: Optional[SourceSpan] = None


@dataclass
class Registry:
    imports:         List[Import] = field(default_factory=list)
    symbols:         List[SymbolEntry] = field(default_factory=list)
    documents:       List[DocumentEntry] = field(default_factory=list)
    collisions:      List[CollisionEntry] = field(default_factory=list)
    invariants:      List[InvariantEntry] = field(default_factory=list)
    promotion_rules: List[PromotionRuleEntry] = field(default_factory=list)
    migrations:      List[MigrationEntry] = field(default_factory=list)
    aliases:         List[Alias] = field(default_factory=list)
    predecessors:    List[Predecessor] = field(default_factory=list)


@dataclass
class Diagnostic:
    code: str
    message: str
    severity: str = "error"
    file: str = ""
    line: int = 0

    def format(self) -> str:
        loc = f"{self.file}:{self.line}: " if self.file else ""
        return f"{self.code} {DIAG_CODES.get(self.code, 'unknown')}: {loc}{self.message}"


# ----------------------------------------------------------------------------
# Preprocess: autolink sanitation (§B.15)
# ----------------------------------------------------------------------------

AUTOLINK_RE = re.compile(r"\[(csr\.[A-Za-z_][A-Za-z0-9_.@#-]*)\]\(http://[^)]*\)")


def preprocess_autolinks(text: str) -> Tuple[str, int]:
    """Strip markdown autolinks of CSR IDs. Returns (cleaned_text, count)."""
    count = len(AUTOLINK_RE.findall(text))
    cleaned = AUTOLINK_RE.sub(r"\1", text)
    return cleaned, count


# ----------------------------------------------------------------------------
# Parser: top-level statements + entry blocks (§25 grammar)
# ----------------------------------------------------------------------------

import yaml  # used for entry block content


class ParseError(Exception):
    pass


def parse(text: str, file_path: str = "") -> Tuple[Registry, List[Diagnostic]]:
    """Parse a .csr file into a Registry AST + diagnostics from preprocess."""
    diagnostics: List[Diagnostic] = []
    text, autolink_count = preprocess_autolinks(text)
    if autolink_count:
        diagnostics.append(Diagnostic(
            code="CSR019",
            message=f"sanitized {autolink_count} autolink(s) before parse",
            severity="info",
            file=file_path,
        ))

    reg = Registry()
    lines = text.split("\n")
    n = len(lines)
    i = 0

    while i < n:
        raw = lines[i]
        line = raw.rstrip()
        stripped = line.strip()
        line_no = i + 1

        # Skip comments and blank lines at top level
        if not stripped or stripped.startswith("#"):
            i += 1
            continue

        # Top-level statements
        m_imp = re.match(r"^import\s+(\S+)\s*$", stripped)
        if m_imp:
            reg.imports.append(Import(
                path=m_imp.group(1),
                source_span=SourceSpan(file=file_path, line=line_no),
            ))
            i += 1
            continue

        m_alias = re.match(r"^alias\s+(\S+)\s*->\s*(\S+)\s*$", stripped)
        if m_alias:
            reg.aliases.append(Alias(
                source=m_alias.group(1),
                target=m_alias.group(2),
                source_span=SourceSpan(file=file_path, line=line_no),
            ))
            i += 1
            continue

        m_pred = re.match(r"^predecessor\s+(\S+)\s*->\s*(\S+)\s*$", stripped)
        if m_pred:
            reg.predecessors.append(Predecessor(
                source=m_pred.group(1),
                target=m_pred.group(2),
                source_span=SourceSpan(file=file_path, line=line_no),
            ))
            i += 1
            continue

        # Entry block: <type> <name>:
        m_entry = re.match(
            r"^(symbol|document|collision|invariant|promotion_rule|migration)\s+(\S+):\s*$",
            line,
        )
        if m_entry:
            entry_type = m_entry.group(1)
            entry_name = m_entry.group(2)
            block_lines: List[str] = []
            i += 1
            while i < n:
                bln = lines[i]
                if bln.startswith("  ") or not bln.strip():
                    block_lines.append(bln)
                    i += 1
                else:
                    break

            # Trim trailing blanks
            while block_lines and not block_lines[-1].strip():
                block_lines.pop()

            block_text = "\n".join(
                bl[2:] if bl.startswith("  ") else bl
                for bl in block_lines
            )
            try:
                parsed: Dict[str, Any] = yaml.safe_load(block_text) or {}
            except yaml.YAMLError as e:
                raise ParseError(
                    f"YAML parse error in {entry_type} {entry_name} at line {line_no}: {e}"
                )

            span = SourceSpan(file=file_path, line=line_no)
            try:
                _attach_entry(reg, entry_type, entry_name, parsed, span)
            except ParseError as pe:
                diagnostics.append(Diagnostic(
                    code="CSR009",
                    message=f"{entry_type} {entry_name}: {pe}",
                    severity="error",
                    file=file_path,
                    line=line_no,
                ))
            continue

        # Unrecognized top-level line - record as diagnostic and skip
        diagnostics.append(Diagnostic(
            code="CSR009",
            message=f"unrecognized top-level line: {stripped[:80]!r}",
            severity="warn",
            file=file_path,
            line=line_no,
        ))
        i += 1

    return reg, diagnostics


def _list(v: Any) -> List[str]:
    if v is None:
        return []
    if isinstance(v, list):
        return [str(x) for x in v]
    return [str(v)]


def _str_or_none(v: Any) -> Optional[str]:
    return None if v is None else str(v)


def _source_anchor_from_dict(d: Optional[Dict[str, Any]]) -> SourceAnchor:
    if not d:
        return SourceAnchor()
    return SourceAnchor(
        document=str(d.get("document", "")),
        version=str(d.get("version", "")),
        section=str(d.get("section", "")),
        anchor=str(d.get("anchor", "")),
        source_hash=_str_or_none(d.get("source_hash")),
        section_hash=_str_or_none(d.get("section_hash")),
        corpus_hash=_str_or_none(d.get("corpus_hash")),
    )


def _verification_from_dict(d: Optional[Dict[str, Any]]) -> VerificationBlock:
    if not d:
        return VerificationBlock()
    evidence_raw = d.get("evidence") or []
    evidence: List[SourceAnchor] = []
    for ev in evidence_raw:
        if isinstance(ev, dict):
            evidence.append(_source_anchor_from_dict(ev))
        else:
            # String shorthand: best-effort split into doc/version/section/anchor
            s = str(ev)
            evidence.append(SourceAnchor(anchor=s))
    return VerificationBlock(
        state=str(d.get("state", "declared")),
        method=str(d.get("method", "prose")),
        last_verified=str(d.get("last_verified", "")),
        evidence=evidence,
    )


def _relations_from_dict(d: Optional[Dict[str, Any]]) -> RelationBlock:
    if not d:
        return RelationBlock()
    return RelationBlock(
        depends_on=_list(d.get("depends_on")),
        refines=_list(d.get("refines")),
        instantiates=_list(d.get("instantiates")),
        used_by=_list(d.get("used_by")),
        conflicts_with=_list(d.get("conflicts_with")),
        equivalent_to=_list(d.get("equivalent_to")),
        contains=_list(d.get("contains")),
        component_of=_list(d.get("component_of")),
        composes_with=_list(d.get("composes_with")),
        xref_only=_list(d.get("xref_only")),
    )


def _attach_entry(
    reg: Registry,
    entry_type: str,
    name: str,
    d: Dict[str, Any],
    span: SourceSpan,
) -> None:
    if entry_type == "symbol":
        sym = SymbolEntry(
            id=str(d.get("id", "")),
            namespace=str(d.get("namespace", "")),
            framework_layer=str(d.get("framework_layer", "")),
            owning_document=str(d.get("owning_document", "")),
            display_name=str(d.get("display_name", name)),
            type=str(d.get("type", "concept")),
            status=str(d.get("status", "candidate")),
            promotion_target=_str_or_none(d.get("promotion_target")),
            applies_to=_list(d.get("applies_to")),
            definition_home=str(d.get("definition_home", "")),
            definition=str(d.get("definition", "")),
            definition_hash=str(d.get("definition_hash", "auto")),
            source_anchor=_source_anchor_from_dict(d.get("source_anchor")),
            components=_list(d.get("components")),
            relations=_relations_from_dict(d.get("relations")),
            verification=_verification_from_dict(d.get("verification")),
            supersedes=_list(d.get("supersedes")),
            superseded_by=_list(d.get("superseded_by")),
            notation=(d.get("notation") if isinstance(d.get("notation"), dict) else None),
            source_span=span,
        )
        reg.symbols.append(sym)
    elif entry_type == "document":
        reg.documents.append(DocumentEntry(
            id=str(d.get("id", "")),
            namespace=str(d.get("namespace", "")),
            display_name=str(d.get("display_name", name)),
            version=str(d.get("version", "")),
            status=str(d.get("status", "candidate")),
            promotion_target=_str_or_none(d.get("promotion_target")),
            defines=_list(d.get("defines")),
            depends_on=_list(d.get("depends_on")),
            publication_mode=str(d.get("publication_mode", "internal")),
            last_verified=str(d.get("last_verified", "")),
            source_path=_str_or_none(d.get("source_path")),
            source_span=span,
        ))
    elif entry_type == "collision":
        reg.collisions.append(CollisionEntry(
            id=str(d.get("id", "")),
            status=str(d.get("status", "candidate")),
            resolution=str(d.get("resolution", "pending")),
            entries=_list(d.get("entries")),
            resolution_note=_str_or_none(d.get("resolution_note")),
            resolved_at=_str_or_none(d.get("resolved_at")),
            possible_resolutions=_list(d.get("possible_resolutions")),
            note=_str_or_none(d.get("note")),
            owner=str(d.get("owner", "")),
            last_verified=str(d.get("last_verified", "")),
            source_span=span,
        ))
    elif entry_type == "invariant":
        reg.invariants.append(InvariantEntry(
            name=name,
            rule=str(d.get("rule", "")),
            severity=str(d.get("severity", "error")),
            source_span=span,
        ))
    elif entry_type == "promotion_rule":
        reg.promotion_rules.append(PromotionRuleEntry(
            name=name,
            requires=_list(d.get("requires")),
            source_span=span,
        ))
    elif entry_type == "migration":
        reg.migrations.append(MigrationEntry(
            name=name,
            from_=str(d.get("from", "")),
            to=str(d.get("to", "")),
            target_wiki_version=str(d.get("target_wiki_version", "")),
            status=str(d.get("status", "candidate")),
            decision=str(d.get("decision", "")),
            replaces=_list(d.get("replaces")),
            renders=_list(d.get("renders")),
            preserves=_list(d.get("preserves")),
            source_span=span,
        ))


# ----------------------------------------------------------------------------
# Locator parsing (B.9) and hash computation (C.6)
# ----------------------------------------------------------------------------

@dataclass
class Locator:
    document_id: str  # csr.document.<DOC>
    version: str
    section: str
    anchor: str

    def render(self) -> str:
        return (
            f"csr.document.{self.document_id.removeprefix('csr.document.')}"
            f"@v{self.version}#section.{self.section}.{self.anchor}"
        )


def parse_locator(s: str) -> Optional[Locator]:
    """Parse the canonical B.9 locator format. Returns None if it doesn't match."""
    m = LOCATOR_RE.match(s.strip())
    if not m:
        return None
    return Locator(
        document_id=f"csr.document.{m.group('doc')}",
        version=m.group("version"),
        section=m.group("section"),
        anchor=m.group("anchor"),
    )


def sha256_hex(s: str) -> str:
    return "sha256:" + hashlib.sha256(s.encode("utf-8")).hexdigest()


def compute_definition_hash(definition: str) -> str:
    """C.6: definition_hash is the hash of canonical registry definition text."""
    return sha256_hex(definition.strip())


# ----------------------------------------------------------------------------
# Validation passes (§B, §C)
# ----------------------------------------------------------------------------

class Validator:
    def __init__(self, reg: Registry):
        self.reg = reg
        self.diagnostics: List[Diagnostic] = []
        # Indexes
        self.symbols_by_id: Dict[str, SymbolEntry] = {}
        self.documents_by_id: Dict[str, DocumentEntry] = {}
        self.collisions_by_id: Dict[str, CollisionEntry] = {}
        self.invariants_by_name: Dict[str, InvariantEntry] = {}

    def emit(self, code: str, message: str, severity: str = "error",
             file: str = "", line: int = 0) -> None:
        self.diagnostics.append(Diagnostic(
            code=code, message=message, severity=severity,
            file=file, line=line,
        ))

    # -- index --------------------------------------------------------------
    def build_indexes(self) -> None:
        for s in self.reg.symbols:
            if s.id in self.symbols_by_id:
                self.emit("CSR001", f"duplicate symbol id: {s.id}",
                          file=_span_file(s), line=_span_line(s))
            else:
                self.symbols_by_id[s.id] = s
        for d in self.reg.documents:
            if d.id in self.documents_by_id:
                self.emit("CSR001", f"duplicate document id: {d.id}",
                          file=_span_file(d), line=_span_line(d))
            else:
                self.documents_by_id[d.id] = d
        for c in self.reg.collisions:
            if c.id in self.collisions_by_id:
                self.emit("CSR001", f"duplicate collision id: {c.id}",
                          file=_span_file(c), line=_span_line(c))
            else:
                self.collisions_by_id[c.id] = c
        for inv in self.reg.invariants:
            if inv.name in self.invariants_by_name:
                self.emit("CSR001", f"duplicate invariant name: {inv.name}",
                          file=_span_file(inv), line=_span_line(inv))
            else:
                self.invariants_by_name[inv.name] = inv

    # -- field validation ---------------------------------------------------
    def validate_fields(self) -> None:
        for s in self.reg.symbols:
            self._validate_symbol_fields(s)
        for d in self.reg.documents:
            self._validate_document_fields(d)
        for c in self.reg.collisions:
            self._validate_collision_fields(c)
        for inv in self.reg.invariants:
            if inv.severity not in SEVERITY_ENUM:
                self.emit("CSR011", f"invariant {inv.name}: invalid severity {inv.severity!r}",
                          file=_span_file(inv), line=_span_line(inv))
        for m in self.reg.migrations:
            if m.status not in STATUS_ENUM:
                self.emit("CSR006", f"migration {m.name}: invalid status {m.status!r}",
                          file=_span_file(m), line=_span_line(m))

    def _validate_symbol_fields(self, s: SymbolEntry) -> None:
        f, ln = _span_file(s), _span_line(s)

        if not s.id:
            self.emit("CSR009", f"symbol {s.display_name or '?'}: missing id",
                      file=f, line=ln)

        if s.status not in STATUS_ENUM:
            self.emit("CSR006", f"symbol {s.id}: invalid status {s.status!r}",
                      file=f, line=ln)

        if s.framework_layer and s.framework_layer not in FRAMEWORK_LAYER_ENUM:
            # Possible namespace/layer conflation
            if s.namespace == s.framework_layer:
                self.emit("CSR017",
                          f"symbol {s.id}: framework_layer {s.framework_layer!r} "
                          f"matches namespace; use a closed-enum framework_layer",
                          file=f, line=ln)
            else:
                self.emit("CSR017",
                          f"symbol {s.id}: invalid framework_layer {s.framework_layer!r}; "
                          f"must be one of {sorted(FRAMEWORK_LAYER_ENUM)}",
                          file=f, line=ln)

        # Locator format check (§B.9)
        if s.definition_home:
            loc = parse_locator(s.definition_home)
            if loc is None:
                self.emit("CSR010",
                          f"symbol {s.id}: definition_home {s.definition_home!r} "
                          f"does not match canonical locator format",
                          file=f, line=ln)

        # Source anchor presence (§C.13)
        if s.status in {"canonical", "provisional", "candidate"}:
            if not s.source_anchor or not s.source_anchor.document:
                self.emit("CSR010",
                          f"symbol {s.id}: missing source_anchor (required for active entries)",
                          file=f, line=ln)
            else:
                if not s.source_anchor.source_hash:
                    self.emit("CSR020",
                              f"symbol {s.id}: source_anchor.source_hash missing",
                              severity="warn", file=f, line=ln)
                if not s.source_anchor.section_hash:
                    self.emit("CSR020",
                              f"symbol {s.id}: source_anchor.section_hash missing",
                              severity="warn", file=f, line=ln)

        # Definition hash presence (§C.13)
        if s.status in {"canonical", "provisional", "candidate"}:
            if not s.definition_hash or s.definition_hash == "auto":
                # 'auto' is a request for the compiler to compute; we'll fill it
                pass
            elif not s.definition_hash.startswith("sha256:"):
                self.emit("CSR009",
                          f"symbol {s.id}: definition_hash must be 'auto' or sha256:...",
                          file=f, line=ln)

        # Verification.last_verified for active entries (§C.13)
        if s.status in {"canonical", "provisional", "candidate"}:
            if not s.verification.last_verified:
                self.emit("CSR011",
                          f"symbol {s.id}: verification.last_verified missing",
                          file=f, line=ln)
            if s.status == "canonical" and s.verification.state == "declared":
                self.emit("CSR007",
                          f"symbol {s.id}: canonical without verification.state >= argued",
                          file=f, line=ln)

        if s.verification.state and s.verification.state not in VERIFICATION_STATE_ENUM:
            self.emit("CSR011",
                      f"symbol {s.id}: invalid verification.state {s.verification.state!r}",
                      file=f, line=ln)
        if s.verification.method and s.verification.method not in VERIFICATION_METHOD_ENUM:
            self.emit("CSR011",
                      f"symbol {s.id}: invalid verification.method {s.verification.method!r}",
                      file=f, line=ln)

        # CSR027 notation_collision_check (warning, opt-in per symbol).
        # Fires when symbols_used declares a plain-capital Latin letter from
        # the reserved set and convention_status is not in the protected
        # statuses. mathcal/mathfrak/etc wrappers do not trigger.
        notation = s.notation if isinstance(s.notation, dict) else None
        if notation is not None:
            symbols_used = notation.get("symbols_used") or []
            if not isinstance(symbols_used, list):
                symbols_used = []
            conv_status = notation.get("convention_status")
            for sym_entry in symbols_used:
                letter = self._extract_plain_letter(str(sym_entry))
                if letter in NOTATION_RESERVED_PLAIN_CAPITALS:
                    if conv_status not in NOTATION_PROTECTED_CONVENTION_STATUSES:
                        self.emit(
                            "CSR027",
                            (
                                f"symbol {s.id}: claims plain Latin capital "
                                f"'{letter}' which is conventionally reserved; "
                                f"mark convention_status as 'convention_adapted' "
                                f"or 'aesthetic_override' with rationale, or "
                                f"rename to mathcal/fraktur variant"
                            ),
                            severity="warn",
                            file=f,
                            line=ln,
                        )

    @staticmethod
    def _extract_plain_letter(sym):
        """Return the plain Latin capital letter if sym is exactly one
        unwrapped capital (e.g. 'A'); else None. Wrappers such as
        'mathcal{A}', 'mathfrak{L}', and subscripted forms like 'V_cert'
        return None and do not collide."""
        s = sym.strip()
        if re.fullmatch(r"[A-Z]", s):
            return s
        return None

    def _validate_document_fields(self, d: DocumentEntry) -> None:
        f, ln = _span_file(d), _span_line(d)
        if not d.id:
            self.emit("CSR009", f"document {d.display_name or '?'}: missing id",
                      file=f, line=ln)
        if d.status not in STATUS_ENUM:
            # Some projects declare compound statuses for back-compat
            # (e.g. "stable (public v1)"). Accept by checking prefix.
            prefix = d.status.split()[0] if d.status else ""
            if prefix not in STATUS_ENUM:
                self.emit("CSR006", f"document {d.id}: invalid status {d.status!r}",
                          file=f, line=ln)

    def _validate_collision_fields(self, c: CollisionEntry) -> None:
        f, ln = _span_file(c), _span_line(c)
        if not c.id:
            self.emit("CSR009", f"collision: missing id",
                      file=f, line=ln)
        if c.resolution not in RESOLUTION_ENUM:
            self.emit("CSR009",
                      f"collision {c.id}: invalid resolution {c.resolution!r}",
                      file=f, line=ln)
        if c.status not in STATUS_ENUM and c.status != "resolved":
            self.emit("CSR006", f"collision {c.id}: invalid status {c.status!r}",
                      file=f, line=ln)

    # -- ID resolution ------------------------------------------------------
    def resolve_aliases(self) -> Dict[str, str]:
        """Returns mapping alias_source -> canonical_id (alias chain flattened)."""
        alias_map: Dict[str, str] = {}
        for a in self.reg.aliases:
            alias_map[a.source] = a.target

        # Flatten chains and detect cycles (CSR015)
        flattened: Dict[str, str] = {}
        for src, tgt in alias_map.items():
            seen = {src}
            cur = tgt
            while cur in alias_map:
                if cur in seen:
                    self.emit("CSR015", f"alias cycle starting at {src}")
                    cur = src  # break
                    break
                seen.add(cur)
                cur = alias_map[cur]
            flattened[src] = cur
            # Validate target exists
            if cur not in self.symbols_by_id and cur not in self.documents_by_id \
               and cur not in self.collisions_by_id and cur not in alias_map:
                self.emit("CSR002", f"alias {src} -> {cur}: target unresolved")
        return flattened

    # -- relations ----------------------------------------------------------
    def resolve_target_kind(self, target_id: str) -> Optional[str]:
        if target_id in self.symbols_by_id:
            return "symbol"
        if target_id in self.documents_by_id:
            return "document"
        if target_id in self.collisions_by_id:
            return "collision"
        if target_id in self.invariants_by_name:
            return "invariant"
        return None

    def validate_relations(self, alias_map: Dict[str, str]) -> None:
        for s in self.reg.symbols:
            f, ln = _span_file(s), _span_line(s)
            for rel in RELATION_TYPES:
                targets = getattr(s.relations, rel)
                allowed_kinds = RELATION_TARGET_TYPES.get(rel, set())
                for tgt in targets:
                    canonical = alias_map.get(tgt, tgt)
                    kind = self.resolve_target_kind(canonical)
                    if kind is None:
                        self.emit("CSR003",
                                  f"symbol {s.id} {rel} -> {tgt}: target unresolved",
                                  file=f, line=ln)
                        continue
                    if allowed_kinds and kind not in allowed_kinds:
                        self.emit("CSR012",
                                  f"symbol {s.id} {rel} -> {tgt}: target kind "
                                  f"{kind!r} not in allowed {sorted(allowed_kinds)}",
                                  file=f, line=ln)

            # Status-of-target dependency rules (§C.8)
            self._validate_target_status(s, alias_map)

    def _validate_target_status(self, s: SymbolEntry, alias_map: Dict[str, str]) -> None:
        f, ln = _span_file(s), _span_line(s)
        for tgt in s.relations.depends_on:
            canonical = alias_map.get(tgt, tgt)
            target = self.symbols_by_id.get(canonical) or self.documents_by_id.get(canonical)
            if target is None:
                continue
            tgt_status = target.status if hasattr(target, "status") else "candidate"
            policy = TARGET_STATUS_DEPENDS_ON.get(tgt_status, "allow")
            if policy == "error":
                self.emit("CSR003",
                          f"symbol {s.id} depends_on {tgt}: target status "
                          f"{tgt_status!r} forbidden",
                          file=f, line=ln)
            elif policy == "warn":
                self.emit("CSR003",
                          f"symbol {s.id} depends_on {tgt}: target status "
                          f"{tgt_status!r} (warning)",
                          severity="warn", file=f, line=ln)
            elif policy == "warn_unless_successor":
                # If deprecated and has superseded_by chain, OK
                if isinstance(target, SymbolEntry) and target.superseded_by:
                    pass  # successor exists, allow
                else:
                    self.emit("CSR003",
                              f"symbol {s.id} depends_on {tgt}: target deprecated "
                              f"without successor",
                              severity="warn", file=f, line=ln)

    # -- inverse derivation (§B.10) -----------------------------------------
    def derive_inverses(self) -> None:
        """Auto-populate inverse edges. Validate user-declared inverses are consistent."""
        sym_index = self.symbols_by_id

        # contains -> component_of, supersedes -> superseded_by
        for forward, inverse in INVERSE_PAIRS.items():
            for s in self.reg.symbols:
                forward_targets = getattr(s.relations, forward, None)
                if forward_targets is None:
                    forward_targets = getattr(s, forward, [])
                if not forward_targets:
                    continue
                for tgt in forward_targets:
                    if tgt not in sym_index:
                        continue
                    target_sym = sym_index[tgt]
                    target_inverse = getattr(target_sym.relations, inverse, None)
                    if target_inverse is None:
                        target_inverse = getattr(target_sym, inverse, None)
                        if target_inverse is None:
                            continue
                    if s.id not in target_inverse:
                        target_inverse.append(s.id)

        # supersedes / superseded_by are top-level fields, not inside relations
        for s in self.reg.symbols:
            for tgt in s.supersedes:
                tgt_sym = sym_index.get(tgt)
                if tgt_sym is None:
                    continue
                if s.id not in tgt_sym.superseded_by:
                    tgt_sym.superseded_by.append(s.id)
            for tgt in s.superseded_by:
                tgt_sym = sym_index.get(tgt)
                if tgt_sym is None:
                    continue
                if s.id not in tgt_sym.supersedes:
                    tgt_sym.supersedes.append(s.id)

        # depends_on -> used_by (one-directional inverse).
        # Writes the reverse edge so "who depends on X" queries can be
        # answered structurally without grepping the lockfile.
        for s in self.reg.symbols:
            for tgt in s.relations.depends_on:
                tgt_sym = sym_index.get(tgt)
                if tgt_sym is None:
                    continue
                if s.id not in tgt_sym.relations.used_by:
                    tgt_sym.relations.used_by.append(s.id)

        # Symmetric: equivalent_to, conflicts_with, composes_with (per §B.10)
        for s in self.reg.symbols:
            for tgt in s.relations.equivalent_to:
                tgt_sym = sym_index.get(tgt)
                if tgt_sym is None:
                    continue
                if s.id not in tgt_sym.relations.equivalent_to:
                    tgt_sym.relations.equivalent_to.append(s.id)
            for tgt in s.relations.conflicts_with:
                tgt_sym = sym_index.get(tgt)
                if tgt_sym is None:
                    continue
                if s.id not in tgt_sym.relations.conflicts_with:
                    tgt_sym.relations.conflicts_with.append(s.id)
            for tgt in s.relations.composes_with:
                tgt_sym = sym_index.get(tgt)
                if tgt_sym is None:
                    continue
                if s.id not in tgt_sym.relations.composes_with:
                    tgt_sym.relations.composes_with.append(s.id)

    # -- cycle policy (§B.11) -----------------------------------------------
    def validate_cycles(self) -> None:
        for rel in CYCLE_ERROR_RELATIONS:
            graph = self._build_relation_graph(rel)
            for cycle in _find_cycles(graph):
                self.emit("CSR008",
                          f"{rel} cycle: {' -> '.join(cycle)} -> {cycle[0]}")

    def validate_prose_version_embeds(self, corpus_root) -> None:
        """CSR025: warn when a document's source file contains prose-embedded
        version citations like "AI v1.2 §17" outside allow-listed contexts.

        Policy (CSR Spec v0.1.4 Z.13.1): documents cite registry entry names
        rather than versions and section numbers of other documents. CSR holds
        the version ledger; body prose does not.

        Allow-listed lines (versions allowed): \\fancyhead, \\title, \\date,
        \\bibitem, \\textbf{Errata}/\\textbf{Version notes}/\\paragraph{Errata.},
        and any line inside a \\begin{thebibliography} ... \\end{thebibliography}
        block. Lines whose first non-whitespace token is %, // or # are also
        allowed (comments).
        """
        import re
        from pathlib import Path as _P
        if corpus_root is None:
            return
        try:
            import csr_extract as _ce
            legacy = getattr(_ce, "SOURCE_PATHS", {})
        except Exception:
            legacy = {}
        PROSE_VERSION_RE = re.compile(
            r"\b([A-Z][A-Za-z0-9_]*)\s+v[0-9]+(?:\.[0-9]+){0,3}\b"
        )
        # Lines beginning with these tokens are allowed to carry version refs.
        ALLOW_PREFIX = (
            "\\fancyhead", "\\title", "\\author", "\\date",
            "\\bibitem", "\\bibliography", "\\thebibliography",
            "\\hypersetup", "\\pdftitle", "\\setmainfont", "\\usepackage",
            "%", "//", "#",
        )
        # If line contains these substrings, it's a changelog/errata marker.
        ALLOW_SUBSTR = ("\\textbf{Errata}", "\\textbf{Version notes}",
                        "\\paragraph{Errata.}", "\\paragraph{Version notes.}",
                        "Companion documents.", "Supersedes:", "Predecessor name:",
                        "predecessor_version:", "current_version:", "canonical_version:",
                        "source_path:")
        ROOT = _P(corpus_root)
        for d in self.reg.documents:
            rel_str = ""
            if getattr(d, "source_path", None):
                rel_str = str(d.source_path).replace("\\", "/")
            elif d.id in legacy:
                rel_str = str(legacy[d.id]).replace("\\", "/")
            if not rel_str:
                continue
            # Only scan .tex / .md (others are out of policy scope here)
            if not rel_str.lower().endswith((".tex", ".md")):
                continue
            src = ROOT / rel_str
            if not src.exists():
                continue
            try:
                lines = src.read_text(encoding="utf-8", errors="replace").splitlines()
            except Exception:
                continue
            in_bib = False
            hits = 0
            for ln_no, raw in enumerate(lines, start=1):
                line = raw.strip()
                if "\\begin{thebibliography}" in line:
                    in_bib = True
                if in_bib:
                    if "\\end{thebibliography}" in line:
                        in_bib = False
                    continue
                if not line:
                    continue
                if any(line.startswith(p) for p in ALLOW_PREFIX):
                    continue
                if any(s in line for s in ALLOW_SUBSTR):
                    continue
                m = PROSE_VERSION_RE.search(raw)
                if m:
                    hits += 1
                    if hits <= 3:  # cap per-document noise
                        self.emit("CSR025",
                                  f"document {d.id}: prose-embedded version '{m.group(0)}' at {rel_str}:{ln_no} "
                                  "(policy: cite registry entry names rather than versions; see CSR Spec Z.13.1)",
                                  severity="info",
                                  file=str(getattr(d, "source_span", "<documents.csr>")),
                                  line=0)
            if hits > 3:
                self.emit("CSR025",
                          f"document {d.id}: {hits} total prose-embedded version refs in {rel_str} "
                          "(only first 3 reported; full audit: grep ' v[0-9]+ ' in source)",
                          severity="info",
                          file=str(getattr(d, "source_span", "<documents.csr>")),
                          line=0)

    def validate_doc_sources(self, corpus_root) -> None:
        """CSR021: warn when a document has no resolvable source file on disk.

        Resolution chain mirrors the HTML renderer's _pdf_link_for_document:
          1. doc.source_path (preferred, inline schema field)
          2. csr_extract.SOURCE_PATHS legacy table
        For the resolved relative path, tries .pdf, .md, .tex (whichever exists).
        Emits CSR021 (warn) when none of the candidates exist on disk.
        """
        from pathlib import Path as _P
        if corpus_root is None:
            return  # cannot existence-check without root
        try:
            import csr_extract as _ce
            legacy = getattr(_ce, "SOURCE_PATHS", {})
        except Exception:
            legacy = {}

        for d in self.reg.documents:
            rel_str = ""
            if getattr(d, "source_path", None):
                rel_str = str(d.source_path).replace("\\", "/")
            elif d.id in legacy:
                rel_str = str(legacy[d.id]).replace("\\", "/")
            if not rel_str:
                self.emit("CSR023",
                          f"document {d.id}: no source_path declared (and no legacy SOURCE_PATHS fallback)",
                          severity="warn",
                          file=str(getattr(d, "source_span", "<documents.csr>")),
                          line=0)
                continue
            base, dot, ext = rel_str.rpartition(".")
            if not base:
                base = rel_str
            candidates = [f"{base}.pdf", f"{base}.md"]
            if ext and ext.lower() != "pdf":
                candidates.append(rel_str)
            seen = set()
            candidates = [c for c in candidates if not (c in seen or seen.add(c))]
            root = _P(corpus_root)
            if not any((root / c).exists() for c in candidates):
                self.emit("CSR021",
                          f"document {d.id}: source declared as {rel_str} but no .pdf/.md/.tex on disk",
                          severity="warn",
                          file=str(getattr(d, "source_span", "<documents.csr>")),
                          line=0)

    def validate_source_hash_drift(self, corpus_root) -> None:
        """CSR004: a pinned source_hash no longer matches the source on disk.

        Only symbols whose source_anchor.source_hash is a pinned sha256 literal
        participate ('auto'/missing are presence-checked by CSR020). Pin hashes
        with tools/compute_hashes.py --force; after a legitimate source change,
        re-verify the affected definitions and re-pin."""
        from pathlib import Path as _P
        import hashlib as _hl
        if corpus_root is None:
            return
        root = _P(corpus_root)
        doc_hash = {}
        for d in self.reg.documents:
            rel = str(getattr(d, "source_path", "") or "").replace("\\", "/")
            if not rel:
                continue
            p = root / rel
            if p.exists():
                h = _hl.sha256()
                h.update(p.read_bytes())
                doc_hash[d.id] = "sha256:" + h.hexdigest()
        for s in self.reg.symbols:
            sa = getattr(s, "source_anchor", None)
            pin = getattr(sa, "source_hash", None) if sa else None
            if not pin or not str(pin).startswith("sha256:"):
                continue
            actual = doc_hash.get(getattr(sa, "document", None))
            if actual and actual != pin:
                self.emit("CSR004",
                          f"symbol {s.id}: source changed after hash pinning "
                          f"(pinned {str(pin)[:18]}.. != current {actual[:18]}..) "
                          f"in {getattr(sa, 'document', '?')}; re-verify the "
                          f"definition, then re-pin with compute_hashes --force",
                          severity="warn",
                          file=str(getattr(s, "source_span", "")), line=0)

    def _build_relation_graph(self, rel: str) -> Dict[str, List[str]]:
        graph: Dict[str, List[str]] = {}
        for s in self.reg.symbols:
            targets = getattr(s.relations, rel, [])
            graph[s.id] = [t for t in targets if t in self.symbols_by_id or t in self.documents_by_id]
        return graph

    # -- definition hashes (§C.6) -------------------------------------------
    def fill_definition_hashes(self) -> None:
        for s in self.reg.symbols:
            if s.definition and (not s.definition_hash or s.definition_hash == "auto"):
                s.definition_hash = compute_definition_hash(s.definition)


def _span_file(obj: Any) -> str:
    span = getattr(obj, "source_span", None)
    return span.file if span else ""


def _span_line(obj: Any) -> int:
    span = getattr(obj, "source_span", None)
    return span.line if span else 0


def _find_cycles(graph: Dict[str, List[str]]) -> List[List[str]]:
    """Return list of cycles (each as list of node IDs)."""
    cycles: List[List[str]] = []
    WHITE, GRAY, BLACK = 0, 1, 2
    color: Dict[str, int] = {n: WHITE for n in graph}
    parent: Dict[str, Optional[str]] = {n: None for n in graph}

    def dfs(u: str) -> None:
        color[u] = GRAY
        for v in graph.get(u, []):
            if v not in color:
                continue
            if color[v] == WHITE:
                parent[v] = u
                dfs(v)
            elif color[v] == GRAY:
                # back edge -> cycle
                cycle = [v]
                w = u
                while w is not None and w != v:
                    cycle.append(w)
                    w = parent[w]
                cycles.append(list(reversed(cycle)))
        color[u] = BLACK

    for n in graph:
        if color[n] == WHITE:
            dfs(n)
    return cycles


# ----------------------------------------------------------------------------
# Lockfile emission (§24)
# ----------------------------------------------------------------------------

def to_jsonable(obj: Any) -> Any:
    """Recursively convert dataclasses to JSON-able structures with sorted keys."""
    if is_dataclass(obj):
        d = {}
        for k, v in asdict(obj).items():
            # Drop source_span (internal) and None defaults
            if k == "source_span":
                continue
            d[k] = to_jsonable(v)
        return d
    if isinstance(obj, list):
        return [to_jsonable(x) for x in obj]
    if isinstance(obj, dict):
        return {k: to_jsonable(v) for k, v in obj.items()}
    return obj


def emit_lockfile(reg: Registry, compiled_at: str = "") -> Dict[str, Any]:
    """Build deterministic lockfile dict per §24."""
    symbols_dict = {}
    for s in sorted(reg.symbols, key=lambda x: x.id):
        sd = to_jsonable(s)
        sd.pop("id", None)  # ID is the key
        symbols_dict[s.id] = sd

    documents_dict = {}
    for d in sorted(reg.documents, key=lambda x: x.id):
        dd = to_jsonable(d)
        dd.pop("id", None)
        documents_dict[d.id] = dd

    collisions_dict = {}
    for c in sorted(reg.collisions, key=lambda x: x.id):
        cd = to_jsonable(c)
        cd.pop("id", None)
        collisions_dict[c.id] = cd

    aliases_dict = {a.source: a.target for a in sorted(reg.aliases, key=lambda x: x.source)}
    predecessors_dict = {p.source: p.target for p in sorted(reg.predecessors, key=lambda x: x.source)}

    invariants_dict = {}
    for inv in sorted(reg.invariants, key=lambda x: x.name):
        invariants_dict[inv.name] = {"rule": inv.rule, "severity": inv.severity}

    promotion_rules_dict = {}
    for pr in sorted(reg.promotion_rules, key=lambda x: x.name):
        promotion_rules_dict[pr.name] = {"requires": pr.requires}

    migrations_dict = {}
    for m in sorted(reg.migrations, key=lambda x: x.name):
        md = to_jsonable(m)
        md.pop("name", None)
        migrations_dict[m.name] = md

    return {
        "registry": "CSR",
        "version": "0.1.1",
        "compiled_at": compiled_at,
        "symbols": symbols_dict,
        "documents": documents_dict,
        "collisions": collisions_dict,
        "aliases": aliases_dict,
        "predecessors": predecessors_dict,
        "invariants": invariants_dict,
        "promotion_rules": promotion_rules_dict,
        "migrations": migrations_dict,
    }


# ----------------------------------------------------------------------------
# Phase 1D: rendered outputs (operator-facing views)
# ----------------------------------------------------------------------------

def _short_hash(h: Optional[str]) -> str:
    if not h:
        return "-"
    if h.startswith("sha256:") and len(h) > 14:
        return h[:14] + "..."
    return h


def render_symbols_md(reg: Registry, compiled_at: str) -> str:
    lines = [
        f"# CSR Symbol Registry",
        f"",
        f"*Rendered output of CSR.lock.json. Non-authoritative. Regenerated each compile.*",
        f"*Compiled at: {compiled_at}*",
        f"",
        f"Total symbols: {len(reg.symbols)}",
        f"",
        f"| ID | Display | Type | Status | Layer | Definition home | Hash |",
        f"|---|---|---|---|---|---|---|",
    ]
    for s in sorted(reg.symbols, key=lambda x: x.id):
        lines.append(
            f"| `{s.id}` "
            f"| {s.display_name} "
            f"| {s.type} "
            f"| {s.status} "
            f"| {s.framework_layer} "
            f"| `{s.definition_home}` "
            f"| `{_short_hash(s.definition_hash)}` |"
        )
    lines.append("")
    return "\n".join(lines)


def render_documents_md(reg: Registry, compiled_at: str) -> str:
    lines = [
        f"# CSR Document Registry",
        f"",
        f"*Rendered output of CSR.lock.json. Non-authoritative. Regenerated each compile.*",
        f"*Compiled at: {compiled_at}*",
        f"",
        f"Total documents: {len(reg.documents)}",
        f"",
        f"| Document | Version | Status | Defines | Depends on | Last verified |",
        f"|---|---|---|---|---|---|",
    ]
    for d in sorted(reg.documents, key=lambda x: x.id):
        defines_str = "; ".join(d.defines) if d.defines else "(none)"
        depends_str = "; ".join(d.depends_on) if d.depends_on else "(none)"
        lines.append(
            f"| `{d.id}` | {d.version} | {d.status} "
            f"| {defines_str} | {depends_str} | {d.last_verified} |"
        )
    lines.append("")
    return "\n".join(lines)


def render_collisions_md(reg: Registry, compiled_at: str) -> str:
    lines = [
        f"# CSR Collision Register",
        f"",
        f"*Rendered output of CSR.lock.json. Non-authoritative. Regenerated each compile.*",
        f"*Compiled at: {compiled_at}*",
        f"",
        f"Total collisions: {len(reg.collisions)}",
        f"",
        f"| Collision ID | Status | Resolution | Entries | Owner | Resolved at | Note |",
        f"|---|---|---|---|---|---|---|",
    ]
    for c in sorted(reg.collisions, key=lambda x: x.id):
        entries_str = "; ".join(c.entries) if c.entries else "-"
        resolved_at = c.resolved_at or "-"
        note = c.resolution_note or c.note or ""
        if note and len(note) > 80:
            note = note[:77] + "..."
        lines.append(
            f"| `{c.id}` | {c.status} | {c.resolution} "
            f"| {entries_str} | {c.owner} | {resolved_at} | {note} |"
        )
    lines.append("")
    return "\n".join(lines)

def render_status_md(reg, compiled_at):
    lines = [
        "# CSR Proof / Status Table",
        "",
        "*Rendered output of CSR.lock.json. Non-authoritative. Regenerated each compile.*",
        f"*Compiled at: {compiled_at}*",
        "",
        "Status records corpus commitment; verification records proof standing.",
        "",
        "| Symbol | Status | Verification state | Method | Evidence | Last verified |",
        "|---|---|---|---|---|---|",
    ]
    for s in sorted(reg.symbols, key=lambda x: x.id):
        v = s.verification
        evidence_count = len(v.evidence) if v.evidence else 0
        lines.append(
            f"| `{s.id}` | {s.status} | {v.state} "
            f"| {v.method} | {evidence_count} anchor(s) | {v.last_verified} |"
        )
    lines.extend([
        "",
        "## Status taxonomy",
        "",
        "- `draft`: newly declared",
        "- `candidate`: actively developed",
        "- `provisional`: stable enough for downstream use",
        "- `canonical`: load-bearing corpus commitment",
        "- `deprecated`: replaced but retained for lineage",
        "- `rejected`: removed from active corpus after review",
        "- `deferred`: v0 placeholder pending v0.1 revisit",
        "",
    ])
    return "\n".join(lines)


def render_dependencies_dot(reg, compiled_at):
    """DOT graph of typed relations between symbols and documents."""
    lines = [
        "// CSR dependency graph",
        f"// Compiled at: {compiled_at}",
        "// Rendered output of CSR.lock.json. Non-authoritative.",
        "digraph CSR {",
        "  rankdir=LR;",
        '  node [shape=box, fontname="monospace", fontsize=10];',
        '  edge [fontname="monospace", fontsize=8];',
        "",
    ]
    by_ns = {}
    for s in reg.symbols:
        by_ns.setdefault(s.namespace or "_unknown", []).append(s)

    status_color = {
        "canonical": "lightblue", "candidate": "lightyellow",
        "provisional": "lightgreen", "deprecated": "lightgray",
        "rejected": "lightcoral", "deferred": "lightgray",
        "draft": "white",
    }

    for ns in sorted(by_ns):
        lines.append(f'  subgraph cluster_{ns} {{')
        lines.append(f'    label="{ns}";')
        lines.append('    style=dashed;')
        for s in sorted(by_ns[ns], key=lambda x: x.id):
            color = status_color.get(s.status, "white")
            lines.append(f'    "{s.id}" [style=filled, fillcolor="{color}"];')
        lines.append("  }")
        lines.append("")

    edge_styles = {
        "depends_on":     ("solid", "black"),
        "refines":        ("dashed", "darkgreen"),
        "instantiates":   ("solid", "darkblue"),
        "equivalent_to":  ("solid", "purple"),
        "conflicts_with": ("solid", "red"),
        "used_by":        ("dotted", "gray50"),
        "xref_only":      ("dotted", "gray70"),
        "contains":       ("solid", "darkblue"),
    }
    for s in reg.symbols:
        for rel, (style, color) in edge_styles.items():
            for tgt in getattr(s.relations, rel, []):
                lines.append(
                    f'  "{s.id}" -> "{tgt}" '
                    f'[label="{rel}", style={style}, color="{color}"];'
                )
    for d in reg.documents:
        for sym in d.defines:
            lines.append(
                f'  "{d.id}" -> "{sym}" [label="defines", style=bold, color=darkgreen];'
            )
    lines.append("}")
    lines.append("")
    return "\n".join(lines)


def render_overview_md(reg, compiled_at, errors, warnings):
    """Top-level overview that operators read first."""
    canonical_syms = sum(1 for s in reg.symbols if s.status == "canonical")
    candidate_syms = sum(1 for s in reg.symbols if s.status == "candidate")
    canonical_docs = sum(1 for d in reg.documents if d.status == "canonical")
    candidate_docs = sum(1 for d in reg.documents if d.status == "candidate")
    namespaces = {}
    for s in reg.symbols:
        namespaces[s.namespace or "_unknown"] = namespaces.get(s.namespace or "_unknown", 0) + 1
    lines = [
        "# CSR Overview",
        "",
        "*Rendered output of CSR.lock.json. Non-authoritative. Regenerated each compile.*",
        f"*Compiled at: {compiled_at}*",
        "",
        "## Build state",
        "",
        f"- Errors: **{errors}**",
        f"- Warnings: **{warnings}**",
        "- Lockfile: `build/CSR.lock.json`",
        "- Validation report: `build/CSR.validation.txt`",
        "",
        "## Counts",
        "",
        "| Object | Total | Canonical | Candidate |",
        "|---|---|---|---|",
        f"| Symbols | {len(reg.symbols)} | {canonical_syms} | {candidate_syms} |",
        f"| Documents | {len(reg.documents)} | {canonical_docs} | {candidate_docs} |",
        f"| Collisions | {len(reg.collisions)} | - | - |",
        f"| Aliases | {len(reg.aliases)} | - | - |",
        f"| Invariants | {len(reg.invariants)} | - | - |",
        f"| Migrations | {len(reg.migrations)} | - | - |",
        "",
        "## Symbols by namespace",
        "",
    ]
    for ns, count in sorted(namespaces.items()):
        lines.append(f"- `{ns}`: {count}")
    lines.extend([
        "",
        "## Rendered views",
        "",
        "- `CSR.symbols.md`: full symbol table",
        "- `CSR.documents.md`: document table with defines / depends_on",
        "- `CSR.collisions.md`: resolved and pending collisions",
        "- `CSR.status.md`: status and verification table",
        "- `CSR.dependencies.dot`: dependency graph (Graphviz)",
        "- `CSR.wiki.md`: consolidated registry view",
        "",
        "Render the dependency graph: `dot -Tsvg build/CSR.dependencies.dot > build/CSR.dependencies.svg`",
        "",
    ])
    return "\n".join(lines)


def _short_hash_helper(h):
    if not h:
        return "-"
    if h.startswith("sha256:") and len(h) > 14:
        return h[:14] + "..."
    return h


def render_wiki_md(reg, compiled_at, errors, warnings):
    """Consolidated registry view; regenerated from CSR.lock.json on every compile."""
    canonical_syms = sum(1 for s in reg.symbols if s.status == "canonical")
    candidate_syms = sum(1 for s in reg.symbols if s.status == "candidate")
    canonical_docs = sum(1 for d in reg.documents if d.status == "canonical")
    candidate_docs = sum(1 for d in reg.documents if d.status == "candidate")
    out = []
    out.extend([
        "# Corpus Semantic Registry: Live View",
        "",
        "*Rendered output of `build/CSR.lock.json`. Non-authoritative.*",
        "*Source of truth: `.csr` files in `registry/`. Compiled at: " + compiled_at + ".*",
        "",
        "---",
        "",
        "## Build state",
        "",
        "| Metric | Value |",
        "|---|---|",
        f"| Errors | **{errors}** |",
        f"| Warnings | **{warnings}** |",
        f"| Symbols | {len(reg.symbols)} ({canonical_syms} canonical, {candidate_syms} candidate) |",
        f"| Documents | {len(reg.documents)} ({canonical_docs} canonical, {candidate_docs} candidate) |",
        f"| Collisions | {len(reg.collisions)} |",
        f"| Aliases | {len(reg.aliases)} |",
        f"| Invariants | {len(reg.invariants)} |",
        f"| Migrations | {len(reg.migrations)} |",
        "",
        "---",
        "",
        "## Migration",
        "",
    ])
    for m in sorted(reg.migrations, key=lambda x: x.name):
        out.extend([
            f"### {m.name}",
            "",
            f"- **From:** {m.from_}",
            f"- **To:** {m.to}",
            f"- **Target wiki version:** {m.target_wiki_version}",
            f"- **Status:** {m.status}",
            "",
            f"**Decision:** {m.decision}",
            "",
        ])
        if m.replaces:
            out.append("**Replaces:**")
            for r in m.replaces:
                out.append(f"- {r}")
            out.append("")
        if m.renders:
            out.append("**Renders:**")
            for r in m.renders:
                out.append(f"- {r}")
            out.append("")
        if m.preserves:
            out.append("**Preserves:**")
            for r in m.preserves:
                out.append(f"- {r}")
            out.append("")

    out.extend(["---", "", "## Document Registry", ""])
    for d in sorted(reg.documents, key=lambda x: x.id):
        out.append(f"### {d.display_name} ({d.namespace})")
        out.append("")
        out.append(f"- **ID:** `{d.id}`")
        out.append(f"- **Version:** {d.version}")
        out.append(f"- **Status:** {d.status}")
        if d.promotion_target:
            out.append(f"- **Promotion target:** {d.promotion_target}")
        out.append(f"- **Publication mode:** {d.publication_mode}")
        out.append(f"- **Last verified:** {d.last_verified}")
        if d.defines:
            out.append("- **Defines:**")
            for sym in d.defines:
                out.append(f"  - `{sym}`")
        if d.depends_on:
            out.append("- **Depends on:**")
            for dep in d.depends_on:
                out.append(f"  - `{dep}`")
        out.append("")

    out.extend(["---", "", "## Symbol Registry", ""])
    by_ns = {}
    for s in reg.symbols:
        by_ns.setdefault(s.namespace or "_unknown", []).append(s)
    for ns in sorted(by_ns):
        out.append(f"### Namespace: `{ns}`")
        out.append("")
        for s in sorted(by_ns[ns], key=lambda x: x.id):
            out.append(f"#### `{s.id}`")
            out.append("")
            out.append(f"- **Display:** {s.display_name}")
            out.append(f"- **Type:** {s.type}")
            stat = s.status + (f" (promotion target: {s.promotion_target})" if s.promotion_target else "")
            out.append(f"- **Status:** {stat}")
            out.append(f"- **Framework layer:** {s.framework_layer}")
            out.append(f"- **Owning document:** `{s.owning_document}`")
            out.append(f"- **Definition home:** `{s.definition_home}`")
            out.append(f"- **Definition hash:** `{_short_hash_helper(s.definition_hash)}`")
            if s.applies_to:
                out.append(f"- **Applies to:** {', '.join(s.applies_to)}")
            if s.components:
                out.append(f"- **Components:** {', '.join(s.components)}")
            if s.supersedes:
                out.append(f"- **Supersedes:** {', '.join(s.supersedes)}")
            if s.superseded_by:
                out.append(f"- **Superseded by:** {', '.join(s.superseded_by)}")
            rel_emitted = False
            for rel in RELATION_TYPES:
                targets = getattr(s.relations, rel, [])
                if targets:
                    if not rel_emitted:
                        out.append("- **Relations:**")
                        rel_emitted = True
                    target_str = ", ".join("`" + t + "`" for t in targets)
                    out.append(f"  - `{rel}`: {target_str}")
            out.append("")
            out.append(f"> {s.definition}")
            out.append("")
            v = s.verification
            out.append(f"*Verification: {v.state} via {v.method}; last verified {v.last_verified}.*")
            out.append("")

    out.extend(["---", "", "## Known Collisions", ""])
    for c in sorted(reg.collisions, key=lambda x: x.id):
        out.append(f"### `{c.id}`")
        out.append("")
        out.append(f"- **Status:** {c.status}")
        out.append(f"- **Resolution:** `{c.resolution}`")
        if c.resolved_at:
            out.append(f"- **Resolved at:** {c.resolved_at}")
        out.append(f"- **Owner:** {c.owner}")
        out.append(f"- **Last verified:** {c.last_verified}")
        if c.entries:
            out.append("- **Entries:**")
            for e in c.entries:
                out.append(f"  - `{e}`")
        if c.possible_resolutions:
            out.append(f"- **Possible resolutions:** {', '.join(c.possible_resolutions)}")
        if c.resolution_note:
            out.append("")
            out.append(f"> {c.resolution_note}")
        if c.note and c.note != c.resolution_note:
            out.append("")
            out.append(f"> *Note:* {c.note}")
        out.append("")

    out.extend(["---", "", "## Aliases", ""])
    if reg.aliases:
        out.append("| Alias | Resolves to |")
        out.append("|---|---|")
        for a in sorted(reg.aliases, key=lambda x: x.source):
            out.append(f"| `{a.source}` | `{a.target}` |")
    else:
        out.append("*(none)*")
    out.append("")

    out.extend(["---", "", "## Invariants", ""])
    if reg.invariants:
        out.append("| Invariant | Rule | Severity |")
        out.append("|---|---|---|")
        for inv in sorted(reg.invariants, key=lambda x: x.name):
            out.append(f"| `{inv.name}` | {inv.rule} | {inv.severity} |")
    out.append("")
    out.extend([
        "---",
        "",
        "*End of live view. Regenerate with `python3 tools/csr_compile.py registry/*.csr`.*",
        "",
    ])
    return "\n".join(out)




def _pdf_link_for_document(doc_id, target_section="", reg=None, corpus_root=None):
    """Return a relative path (from build/) to the most-readable file for this document.
    Resolution order:
      1. doc.source_path on the Registry document entry (preferred; matches the new schema).
      2. csr_extract.SOURCE_PATHS legacy table.
    Fallback chain on the resolved relative path: .pdf -> .md -> .tex (first that exists),
    then 00_All_PDFs/<basename>.pdf (consolidated publish dir per watch.py PUBLISH_DIR).
    Returns empty string when no readable file is on disk.
    Existence-checking requires corpus_root; if not provided, the legacy behaviour
    (.tex -> swap to .pdf, no existence check) is used."""
    from pathlib import Path as _P

    rel_str = ""

    # Step 1: prefer doc.source_path on the registry
    if reg is not None:
        for d in reg.documents:
            if d.id == doc_id and getattr(d, "source_path", None):
                rel_str = str(d.source_path).replace("\\", "/")
                break

    # Step 2: fall back to legacy SOURCE_PATHS table
    if not rel_str:
        if csr_extract is None:
            return ""
        rel = csr_extract.SOURCE_PATHS.get(doc_id)
        if rel is None:
            return ""
        rel_str = str(rel).replace("\\", "/")

    # Strip extension to build candidate list
    base, dot, ext = rel_str.rpartition(".")
    if not base:
        base = rel_str
        ext = ""
    # Bare filename used for consolidated 00_All_PDFs/ lookup
    bare = base.rsplit("/", 1)[-1]

    candidates = []
    # Source-adjacent .pdf, then consolidated publish dir, then .md, then original source.
    # The 00_All_PDFs/ fallback comes BEFORE .md so produced PDFs are preferred when both
    # the .md source and the consolidated PDF are on disk.
    candidates.append(f"{base}.pdf")
    candidates.append(f"00_All_PDFs/{bare}.pdf")
    candidates.append(f"{base}.md")
    if ext and ext.lower() not in ("pdf",):
        candidates.append(rel_str)
    # de-dup preserving order
    seen = set()
    candidates = [c for c in candidates if not (c in seen or seen.add(c))]

    # Step 3: existence-check if corpus_root supplied
    if corpus_root is not None:
        root = _P(corpus_root)
        for c in candidates:
            if (root / c).exists():
                return f"../../../{c}"
        return ""

    # Legacy fallback (no existence check): use .pdf if .tex source, else original
    if rel_str.endswith(".tex"):
        return f"../../../{base}.pdf"
    return f"../../../{rel_str}"


def _render_minimal_markdown(text: str) -> str:
    """Minimal markdown -> HTML conversion for inline manual rendering.
    Handles: # / ## / ### headers, ``` fenced code blocks, blank-line paragraphs.
    Escapes HTML in non-code contexts. Not a full markdown parser."""
    import html as _html_mod
    out = []
    in_code = False
    para = []
    def flush_para():
        if para:
            out.append('<p>' + _html_mod.escape(' '.join(para).strip()) + '</p>')
            para.clear()
    for line in text.split("\n"):
        if line.startswith("```"):
            flush_para()
            if in_code:
                out.append('</code></pre>')
                in_code = False
            else:
                out.append('<pre class="manual-code"><code>')
                in_code = True
            continue
        if in_code:
            out.append(_html_mod.escape(line))
            continue
        if line.startswith("### "):
            flush_para()
            out.append(f'<h4 class="manual-h4">{_html_mod.escape(line[4:].strip())}</h4>')
        elif line.startswith("## "):
            flush_para()
            out.append(f'<h3 class="manual-h3">{_html_mod.escape(line[3:].strip())}</h3>')
        elif line.startswith("# "):
            flush_para()
            out.append(f'<h2 class="manual-h2">{_html_mod.escape(line[2:].strip())}</h2>')
        elif line.strip() == "":
            flush_para()
        else:
            para.append(line.strip())
    flush_para()
    if in_code:
        out.append('</code></pre>')
    return "\n".join(out)


def render_registry_html(reg, compiled_at, errors, warnings, corpus_root=None):
    """Clean, fast, no-source-extraction registry browser.

    Shows registry metadata + clickable cross-references + 'open source PDF'
    links for each entry. No pandoc, no KaTeX, no extraction. The consolidated
    wiki snapshot (CSR.wiki.md/.html) handles prose-embedding separately."""
    import html as _html

    canonical_syms = sum(1 for s in reg.symbols if s.status == "canonical")
    candidate_syms = sum(1 for s in reg.symbols if s.status == "candidate")
    canonical_docs = sum(1 for d in reg.documents if d.status == "canonical")
    candidate_docs = sum(1 for d in reg.documents if d.status == "candidate")

    known_symbol_ids = {s.id for s in reg.symbols}
    known_document_ids = {d.id for d in reg.documents}

    def esc(s):
        return _html.escape(str(s)) if s is not None else ""

    def status_badge(status):
        return f'<span class="badge {esc(status)}">{esc(status)}</span>'

    def sym_anchor(sid):
        return "sym-" + re.sub(r"[^A-Za-z0-9]", "-", sid)

    def doc_anchor(did):
        return "doc-" + re.sub(r"[^A-Za-z0-9]", "-", did)

    def linkify_id(token):
        token = token.strip()
        if token in known_symbol_ids:
            return f'<a class="xref" href="#{sym_anchor(token)}"><code>{esc(token)}</code></a>'
        if token in known_document_ids:
            return f'<a class="xref" href="#{doc_anchor(token)}"><code>{esc(token)}</code></a>'
        return f'<code>{esc(token)}</code>'

    def pdf_button(doc_id, label):
        href = _pdf_link_for_document(doc_id, reg=reg, corpus_root=corpus_root)
        if not href:
            return f'<span class="pdf-link unavailable">{esc(label)}</span>'
        return f'<a class="pdf-link" href="{esc(href)}" target="_blank" rel="noopener">{esc(label)} ↗</a>'

    css = """
:root {
  /* Color (dark mode default) */
  --bg: #14171a; --fg: #e8e8e8; --muted: #8a8e96; --border: #2c3038;
  --code-bg: #1d2025; --accent: #5fa66a;
  --sidebar-bg: #1a1d22; --tint-hover: rgba(95, 166, 106, 0.10);
  --tint-open: rgba(95, 166, 106, 0.16); --tint-scroll: rgba(255,255,255,0.16);
  --tint-scroll-hover: rgba(255,255,255,0.30);
  --canonical-bg: #1a3d27; --canonical-fg: #b6e6c4;
  --candidate-bg: #463a10; --candidate-fg: #ffe89e;
  --provisional-bg: #1e4030; --provisional-fg: #b9f0c9;
  --deprecated-bg: #2a2c30; --deprecated-fg: #b0b0b0;
  --rejected-bg: #4a1d1d; --rejected-fg: #ffb3b3;
  --deferred-bg: #2e1d52; --deferred-fg: #d6c2ff;
  --resolved-bg: #1e4030; --resolved-fg: #b9f0c9;

  /* Type: golden minor (sqrt phi = 1.272) from 14px base */
  --fs-xs: 0.78rem; --fs-sm: 0.88rem; --fs-md: 0.94rem; --fs-base: 1rem;
  --fs-h3: 1.272rem; --fs-h2: 1.618rem; --fs-h1: 2.058rem;

  /* Space: 1.5x rhythm; sp-6/sp-7 expand to phi^2 phi^3 for major breaks */
  --sp-1: 0.25rem; --sp-2: 0.5rem; --sp-3: 0.75rem; --sp-4: 1rem;
  --sp-5: 1.5rem; --sp-6: 2.5rem; --sp-7: 4rem;

  /* Layout: sidebar : content = 1 : phi^2 */
  --sidebar-w: 14rem; --content-max: 54rem;
  --radius: 3px; --radius-pill: 999px;
}
* { box-sizing: border-box; }
body {
  margin: 0; font-family: -apple-system, "Segoe UI", Roboto, "Helvetica Neue", sans-serif;
  font-size: 14px; line-height: 1.55; color: var(--fg); background: var(--bg);
  font-feature-settings: "kern" 1, "liga" 1;
}

/* Layout: sidebar is the only architectural column boundary */
.layout { display: flex; min-height: 100vh; }
.sidebar {
  width: var(--sidebar-w); flex-shrink: 0;
  background: var(--sidebar-bg); border-right: 1px solid var(--border);
  position: sticky; top: 0; height: 100vh; overflow-y: auto;
  padding: var(--sp-5) var(--sp-4); font-size: var(--fs-sm);
  scrollbar-width: thin;
  scrollbar-color: var(--tint-scroll) transparent;
}
.sidebar::-webkit-scrollbar { width: 5px; }
.sidebar::-webkit-scrollbar-track { background: transparent; }
.sidebar::-webkit-scrollbar-thumb { background: var(--tint-scroll); border-radius: var(--radius); }
.sidebar::-webkit-scrollbar-thumb:hover { background: var(--tint-scroll-hover); }
.sidebar h2 {
  font-size: var(--fs-sm); margin-top: var(--sp-5); margin-bottom: var(--sp-2);
  color: var(--accent); border: none; padding: 0; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.05em;
}
.sidebar h2:first-child { margin-top: 0; }
.sidebar ul { list-style: none; margin: 0; padding-left: var(--sp-3); }
.sidebar li { margin: var(--sp-1) 0; }
.sidebar a { color: var(--fg); text-decoration: none; word-break: break-word; }
.sidebar a:hover { color: var(--accent); }
.sidebar .ns-group, .sidebar .doc-group { margin-bottom: var(--sp-2); }
/* Main-content section collapsibles: Document Registry, Preprint Registry, each Namespace */
details.section { margin: var(--sp-5) 0 var(--sp-3) 0; border-top: 1px solid var(--border); padding-top: var(--sp-3); }
details.section[open] { margin-bottom: var(--sp-5); }
summary.section-heading {
  cursor: pointer; list-style: none;
  font-size: var(--fs-h2); font-weight: 600; line-height: 1.25;
  padding: var(--sp-2) 0; color: var(--fg);
  display: flex; align-items: baseline; gap: var(--sp-2);
}
summary.section-heading::-webkit-details-marker { display: none; }
summary.section-heading::before {
  content: "\\25B8"; font-size: 0.7em; transition: transform 0.15s; color: var(--muted); flex-shrink: 0;
}
details.section[open] > summary.section-heading::before { transform: rotate(90deg); color: var(--accent); }
summary.section-heading:hover { color: var(--accent); }
summary.section-heading-ns { font-size: var(--fs-h3); }
summary.section-heading .h2-count { font-size: var(--fs-base); color: var(--muted); font-weight: 400; }
details.section section.section-body { padding-left: 0; }
.manual-body { padding: var(--sp-2) 0 var(--sp-3) 0; max-width: 56rem; }
.manual-body h2.manual-h2 { font-size: var(--fs-h3); margin: var(--sp-4) 0 var(--sp-2) 0; border: none; padding: 0; }
.manual-body h3.manual-h3 { font-size: var(--fs-base); font-weight: 600; margin: var(--sp-3) 0 var(--sp-1) 0; color: var(--accent); border: none; padding: 0; }
.manual-body h4.manual-h4 { font-size: var(--fs-base); font-weight: 600; margin: var(--sp-2) 0 var(--sp-1) 0; color: var(--fg); border: none; padding: 0; }
.manual-body p { margin: var(--sp-2) 0; line-height: 1.55; }
.manual-body pre.manual-code {
  background: var(--sidebar-bg); border-left: 2px solid var(--accent);
  padding: var(--sp-2) var(--sp-3); margin: var(--sp-2) 0;
  overflow-x: auto; font-size: var(--fs-sm); line-height: 1.45;
}
.manual-body pre.manual-code code { background: transparent; padding: 0; color: var(--fg); }
ul.recent-list { list-style: none; padding-left: 0; margin: var(--sp-2) 0; }
li.recent-item { padding: var(--sp-1) 0; font-size: var(--fs-sm); display: flex; flex-wrap: wrap; align-items: baseline; gap: var(--sp-2); border-bottom: 1px solid var(--border); }
li.recent-item:last-child { border-bottom: none; }
li.recent-item .recent-date { color: var(--muted); font-variant-numeric: tabular-nums; flex-shrink: 0; }
li.recent-item .recent-kind { color: var(--muted); font-size: var(--fs-xs); text-transform: uppercase; letter-spacing: 0.05em; flex-shrink: 0; min-width: 2.5rem; }
li.recent-item .recent-meta { color: var(--muted); font-weight: 400; }
li.recent-item a { color: var(--fg); text-decoration: none; }
li.recent-item a:hover { color: var(--accent); }
.sidebar .ns-label {
  font-weight: 600; color: var(--muted); font-size: var(--fs-xs);
  text-transform: uppercase; letter-spacing: 0.05em; margin-top: var(--sp-2);
  cursor: pointer; list-style: none; padding: var(--sp-1) 0;
  display: flex; align-items: center; gap: var(--sp-2);
}
.sidebar .ns-label::-webkit-details-marker { display: none; }
.sidebar .ns-label::before {
  content: "\\25B8"; font-size: 0.7em; transition: transform 0.15s; color: var(--muted);
}
.sidebar details[open] > .ns-label::before { transform: rotate(90deg); }
.sidebar .ns-label:hover { color: var(--accent); }
.sidebar details[open] > .ns-label { color: var(--fg); }
.sidebar .filter {
  width: 100%; padding: var(--sp-2) var(--sp-2); margin-bottom: var(--sp-4); font-size: var(--fs-sm);
  border: none; border-bottom: 1px solid var(--border); background: transparent;
  border-radius: 0; font-family: inherit; outline: none;
}
.sidebar .filter:focus { border-bottom-color: var(--accent); }

.content {
  flex: 1; padding: var(--sp-5) var(--sp-5) var(--sp-6) var(--sp-5);
  max-width: var(--content-max); margin: 0 auto;
}

/* Page header: compact single-band with build ticker */
.page-head { margin-bottom: var(--sp-5); padding-bottom: var(--sp-3); border-bottom: 1px solid var(--border); }
.page-head h1 { margin: 0 0 var(--sp-2) 0; border: none; padding: 0; font-size: var(--fs-h2); }
.ticker { display: flex; flex-wrap: wrap; gap: var(--sp-4); align-items: baseline; font-size: var(--fs-sm); color: var(--muted); }
.ticker b { color: var(--fg); font-weight: 600; }
.ticker-tail { margin-left: auto; opacity: 0.7; }
.ticker-help { display: inline-block; }
.ticker-help summary { cursor: pointer; list-style: none; padding: 0 var(--sp-1); border-radius: var(--radius); color: var(--muted); }
.ticker-help summary::-webkit-details-marker { display: none; }
.ticker-help summary:hover { color: var(--accent); }
.ticker-help-body { position: absolute; right: var(--sp-5); margin-top: var(--sp-2); max-width: 28rem; padding: var(--sp-3); background: var(--code-bg); border: 1px solid var(--border); border-radius: var(--radius); font-style: normal; color: var(--fg); z-index: 50; }

/* Type rhythm: only h1 / h2 carry baseline rules; everything else uses space */
h1 {
  font-size: var(--fs-h1); margin-top: 0;
  border-bottom: 1px solid var(--fg); padding-bottom: var(--sp-2);
  line-height: 1.2; font-weight: 600; letter-spacing: -0.01em;
}
.h2-count { font-size: var(--fs-sm); color: var(--muted); font-weight: 400; margin-left: var(--sp-2); letter-spacing: normal; }
h2 {
  font-size: var(--fs-h2); margin-top: var(--sp-7); padding-bottom: var(--sp-1);
  border-bottom: 1px solid var(--border); line-height: 1.3; font-weight: 600;
}
h3 {
  font-size: var(--fs-h3); margin-top: var(--sp-6); color: var(--accent);
  line-height: 1.35; font-weight: 600;
}
h4 {
  font-size: var(--fs-base); margin-top: var(--sp-5); padding-top: var(--sp-1);
  font-family: ui-monospace, "SF Mono", Consolas, monospace;
  scroll-margin-top: var(--sp-3); font-weight: 600;
}
h4 .anchor-link {
  font-size: var(--fs-xs); color: var(--muted); text-decoration: none;
  margin-left: var(--sp-2); opacity: 0; transition: opacity 0.15s;
}
h4:hover .anchor-link { opacity: 1; }

/* Code: faint background only, no frame */
code, pre { font-family: ui-monospace, "SF Mono", Consolas, "Menlo", monospace; font-size: 0.92em; }
code { background: var(--code-bg); padding: 0.1em 0.35em; border-radius: var(--radius); }
pre { background: var(--code-bg); padding: var(--sp-3) var(--sp-4); border-radius: var(--radius); overflow-x: auto; border: none; }

.muted { color: var(--muted); font-style: italic; }
.preamble { font-size: var(--fs-sm); color: var(--muted); margin: 0 0 var(--sp-5) 0; }

/* Tables: only header underline, no per-cell grid (tables are not data prisons) */
table { border-collapse: collapse; width: 100%; margin: var(--sp-3) 0 var(--sp-5) 0; font-size: var(--fs-sm); }
th, td { border: none; padding: var(--sp-2) var(--sp-3) var(--sp-2) 0; text-align: left; vertical-align: top; }
th { font-weight: 600; color: var(--muted); font-size: var(--fs-xs); text-transform: uppercase; letter-spacing: 0.05em; border-bottom: 1px solid var(--border); }

/* Status badges: the badge IS the boundary, keep its edges */
.badge { display: inline-block; padding: 0.05rem 0.55rem; border-radius: var(--radius-pill); font-size: var(--fs-xs); font-weight: 600; vertical-align: middle; letter-spacing: 0.02em; }
.badge.canonical    { background: var(--canonical-bg);    color: var(--canonical-fg); }
.badge.candidate    { background: var(--candidate-bg);    color: var(--candidate-fg); }
.badge.provisional  { background: var(--provisional-bg);  color: var(--provisional-fg); }
.badge.deprecated   { background: var(--deprecated-bg);   color: var(--deprecated-fg); }
.badge.rejected     { background: var(--rejected-bg);     color: var(--rejected-fg); }
.badge.deferred     { background: var(--deferred-bg);     color: var(--deferred-fg); }
.badge.resolved     { background: var(--resolved-bg);     color: var(--resolved-fg); }

/* Metrics, definitions, relations: text-only, no frames */
.metric { display: inline-block; margin-right: var(--sp-5); }
.metric .v { font-weight: 700; font-size: var(--fs-h3); }
.metric .l { color: var(--muted); font-size: var(--fs-sm); margin-left: var(--sp-1); }
.def { color: var(--muted); padding: 0; margin: var(--sp-2) 0 var(--sp-4) 0; font-size: var(--fs-md); font-style: italic; }
.relations { font-size: var(--fs-md); }
.relations .rel-type { font-weight: 600; color: var(--accent); }
a.xref { text-decoration: none; }
a.xref code { color: var(--accent); }
a.xref:hover code { background: var(--canonical-bg); }
a.pdf-link {
  display: inline-block; padding: var(--sp-1) var(--sp-3); background: var(--canonical-bg);
  color: var(--canonical-fg); border-radius: var(--radius); text-decoration: none;
  font-size: var(--fs-sm); font-weight: 600;
}
a.pdf-link:hover { background: var(--accent); color: #fff; }
.pdf-link.unavailable { color: var(--muted); font-size: var(--fs-sm); background: transparent; padding: var(--sp-1) 0; }

/* Tag-row entries: airy, no hairlines between them; vertical breath separates */
details.entry { border: none; margin: var(--sp-2) 0; }
details.entry > summary.tag-row {
  display: flex; align-items: center; gap: var(--sp-3); flex-wrap: wrap;
  padding: var(--sp-2) var(--sp-2); cursor: pointer; list-style: none;
  border-radius: var(--radius); transition: background 0.1s;
}
details.entry > summary.tag-row::-webkit-details-marker { display: none; }
details.entry > summary.tag-row:hover { background: var(--tint-hover); }
details.entry[open] > summary.tag-row { background: var(--tint-open); }
details.entry .tag-id code { background: transparent; padding: 0; color: var(--accent); font-weight: 600; font-size: var(--fs-base); }
details.entry .tag-meta { color: var(--muted); font-size: var(--fs-sm); flex-shrink: 0; }
details.entry .tag-gloss {
  color: var(--muted); font-size: var(--fs-sm); font-style: italic;
  flex: 1 1 0; min-width: 0;
  white-space: nowrap; overflow: hidden; text-overflow: ellipsis;
  max-width: 36rem;
}
details.entry[open] .tag-gloss { display: none; }
details.entry .tag-action a.pdf-link { padding: 0.05rem var(--sp-2); font-size: var(--fs-xs); }
details.entry .tag-more { color: var(--muted); font-size: var(--fs-sm); transition: transform 0.15s; margin-left: auto; }
details.entry[open] .tag-more { transform: rotate(180deg); color: var(--accent); }
details.entry .entry-body { padding: var(--sp-2) var(--sp-4) var(--sp-3) var(--sp-4); }
details.entry .entry-fullid { color: var(--muted); font-size: var(--fs-sm); margin: var(--sp-1) 0; }
details.entry .entry-fullid code { background: transparent; padding: 0; color: var(--muted); }
details.entry .entry-gloss { color: var(--fg); font-size: var(--fs-base); margin: var(--sp-2) 0 var(--sp-3) 0; line-height: 1.55; }
details.entry .entry-locator { color: var(--muted); font-size: var(--fs-sm); margin-bottom: var(--sp-2); }
details.entry .entry-table { font-size: var(--fs-sm); margin: var(--sp-2) 0; }

/* Sidebar collapse toggle:
   - Default (sidebar visible): button anchored at top-left of the text
     section, just past the sidebar's right edge. Icon "<" reads as the
     action "close" (collapse leftward).
   - Hidden state: button moves to viewport corner-pin. Icon flipped to
     a hamburger via CSS so it reads as "open / show menu". */
.sidebar-toggle {
  position: fixed;
  top: var(--sp-3);
  left: calc(var(--sidebar-w) + var(--sp-2));
  z-index: 100;
  background: transparent; color: var(--muted);
  border: 1px solid var(--border); border-radius: var(--radius);
  width: 1.4rem; height: 1.4rem; padding: 0;
  font-size: var(--fs-sm); line-height: 1; cursor: pointer;
  display: flex; align-items: center; justify-content: center;
  transition: color 0.12s, border-color 0.12s, background 0.12s,
              opacity 0.12s, left 0.18s ease;
  opacity: 0.55;
}
.sidebar-toggle:hover { color: var(--accent); border-color: var(--accent); background: var(--tint-hover); opacity: 1; }
body.sidebar-hidden .sidebar-toggle { left: var(--sp-3); opacity: 0.45; }
body.sidebar-hidden .sidebar-toggle:hover { opacity: 1; }
@media (max-width: 1100px) {
  .sidebar-toggle { left: var(--sp-3); }
}
body.sidebar-hidden .sidebar { display: none; }
body.sidebar-hidden .content { max-width: 66rem; padding-left: var(--sp-6); padding-right: var(--sp-6); }
@media (max-width: 1100px) {
  .sidebar { display: none; }
  body:not(.sidebar-shown) .content { max-width: none; padding: var(--sp-4); }
}

/* View-switch banner: inline note, faint background, no frame */
.view-switch {
  background: rgba(240, 160, 43, 0.12); padding: var(--sp-3) var(--sp-4); border: none;
  margin: var(--sp-2) 0 var(--sp-5) 0; border-radius: var(--radius); font-size: var(--fs-md);
}
"""

    js = """
(function() {
  // Sidebar toggle (T key or button)
  var toggle = document.getElementById('sidebar-toggle');
  function syncToggleIcon() {
    if (!toggle) return;
    var hidden = document.body.classList.contains('sidebar-hidden');
    toggle.textContent = hidden
      ? (toggle.getAttribute('data-icon-closed') || '\u2630')
      : (toggle.getAttribute('data-icon-open') || '<');
    toggle.setAttribute('aria-label', hidden ? 'Show sidebar' : 'Hide sidebar');
  }
  if (toggle) {
    toggle.addEventListener('click', function() {
      document.body.classList.toggle('sidebar-hidden');
      try { localStorage.setItem('csr-sidebar-hidden', document.body.classList.contains('sidebar-hidden') ? '1' : '0'); } catch (e) {}
      syncToggleIcon();
    });
    try {
      if (localStorage.getItem('csr-sidebar-hidden') === '1') {
        document.body.classList.add('sidebar-hidden');
      }
    } catch (e) {}
    syncToggleIcon();
  }
  document.addEventListener('keydown', function(e) {
    if (e.key === 't' && !e.target.matches('input, textarea')) {
      document.body.classList.toggle('sidebar-hidden');
      syncToggleIcon();
    }
  });

  var input = document.getElementById('toc-filter');
  if (!input) return;
  // Track which sidebar details the filter forced open, so we can restore
  // their default-closed state when the filter is cleared.
  var filterForcedOpen = [];
  input.addEventListener('input', function() {
    var q = this.value.trim().toLowerCase();
    document.querySelectorAll('.sidebar li[data-id]').forEach(function(li) {
      var id = li.getAttribute('data-id').toLowerCase();
      li.style.display = (q === '' || id.indexOf(q) !== -1) ? '' : 'none';
    });
    document.querySelectorAll('.sidebar .ns-group, .sidebar .doc-group').forEach(function(g) {
      var visible = g.querySelectorAll('li[data-id]:not([style*="display: none"])').length;
      g.style.display = visible > 0 ? '' : 'none';
      // Force-open any group with at least one visible match, so the filter
      // is visible without the user clicking through every collapsed group.
      if (q !== '' && visible > 0 && !g.open) {
        g.open = true;
        filterForcedOpen.push(g);
      }
    });
    // Filter cleared: collapse groups the filter forced open, restoring
    // the default-collapsed state.
    if (q === '' && filterForcedOpen.length) {
      filterForcedOpen.forEach(function(g) { g.open = false; });
      filterForcedOpen = [];
    }
  });

  // Hash-target auto-expand: when navigating to a symbol via anchor, open
  // its <details> instead of merely scrolling past a collapsed row.
  function expandHashTarget() {
    var hash = window.location.hash;
    if (!hash || hash.length < 2) return;
    var el = document.getElementById(hash.slice(1));
    if (!el) return;
    if (el.tagName === 'DETAILS' && !el.open) {
      el.open = true;
    }
    // Always walk ancestors: with section-level wrappers (Document Registry,
    // each Namespace), an inner entry's ancestor section must open too.
    var p = el.parentElement;
    while (p && p !== document.body) {
      if (p.tagName === 'DETAILS' && !p.open) p.open = true;
      p = p.parentElement;
    }
    // Re-scroll after expand so the row is visible.
    setTimeout(function() {
      el.scrollIntoView({ block: 'start', behavior: 'smooth' });
    }, 30);
  }
  expandHashTarget();
  window.addEventListener('hashchange', expandHashTarget);
  // Catch clicks on internal hash links so the same logic runs even when
  // the hash didn't change (re-clicking the same link).
  document.addEventListener('click', function(e) {
    var a = e.target.closest && e.target.closest('a[href^="#"]');
    if (!a) return;
    var href = a.getAttribute('href');
    if (!href || href.length < 2) return;
    var el = document.getElementById(href.slice(1));
    if (!el) return;
    if (el.tagName === 'DETAILS' && !el.open) el.open = true;
    var p = el.parentElement;
    while (p && p !== document.body) {
      if (p.tagName === 'DETAILS' && !p.open) p.open = true;
      p = p.parentElement;
    }
  });
})();
"""

    by_ns = {}
    for s in reg.symbols:
        by_ns.setdefault(s.namespace or "_unknown", []).append(s)

    toc_lines = []
    toc_lines.append('<input class="filter" id="toc-filter" placeholder="Filter symbols..." />')
    toc_lines.append('<h2>Sections</h2><ul>')
    # build-state moved into compact header; no separate TOC link
    toc_lines.append('<li><a href="#document-registry">Document Registry</a></li>')
    toc_lines.append('<li><a href="#preprint-registry">Preprint Registry</a></li>')
    toc_lines.append('<li><a href="#symbol-registry">Symbol Registry</a></li>')
    toc_lines.append('<li><a href="#collisions">Known Collisions</a></li>')
    toc_lines.append('<li><a href="#aliases">Aliases</a></li>')
    toc_lines.append('<li><a href="#invariants">Invariants</a></li>')
    toc_lines.append('</ul>')
    toc_lines.append('<h2>Symbols by namespace</h2>')
    for ns in sorted(by_ns):
        toc_lines.append(f'<details class="ns-group" data-ns="{esc(ns)}">')
        toc_lines.append(f'<summary class="ns-label">{esc(ns)}</summary>')
        toc_lines.append('<ul>')
        for s in sorted(by_ns[ns], key=lambda x: x.id):
            toc_lines.append(
                f'<li data-id="{esc(s.id)}"><a href="#{sym_anchor(s.id)}">'
                f'<code>{esc(s.id.replace("csr." + ns + ".", ""))}</code></a></li>'
            )
        toc_lines.append('</ul></details>')
    toc_lines.append('<details class="doc-group"><summary class="ns-label">Documents</summary><ul>')
    for d in sorted(reg.documents, key=lambda x: x.id):
        short = d.id.replace("csr.document.", "")
        toc_lines.append(
            f'<li data-id="{esc(d.id)}"><a href="#{doc_anchor(d.id)}">'
            f'<code>{esc(short)}</code></a></li>'
        )
    toc_lines.append('</ul></details>')

    out = []
    out.append("<!DOCTYPE html>")
    out.append('<html lang="en"><head><meta charset="utf-8">')
    out.append("<title>CSR Registry Browser</title>")
    out.append(f"<style>{css}</style></head><body>")
    out.append('<div class="layout">')
    out.append('<aside class="sidebar">')
    out.extend(toc_lines)
    out.append('</aside>')
    out.append('<button class="sidebar-toggle" id="sidebar-toggle" title="Toggle sidebar (T key)" aria-label="Toggle sidebar" data-icon-open="&lt;" data-icon-closed="\u2630">&lt;</button>')
    out.append('<main class="content">')
    # Compact header: H1 + single-line build ticker. The verbose preamble,
    # view-switch banner, and metric-tile pile have all collapsed into the
    # ticker. Snapshot link is a footnote-style anchor in <details> so it
    # only appears when the user wants it.
    out.append('<header class="page-head" id="build-state">')
    out.append('<h1>Corpus Semantic Registry</h1>')
    out.append('<div class="ticker">')
    out.append(f'<span><b>{len(reg.symbols)}</b> symbols</span>')
    out.append(f'<span><b>{len(reg.documents)}</b> documents</span>')
    out.append(f'<span><b>{errors}</b> err / <b>{warnings}</b> warn</span>')
    out.append(f'<span class="ticker-tail">{esc(compiled_at[:10])} · <details class="ticker-help"><summary>?</summary><div class="ticker-help-body">Rendered from <code>build/CSR.lock.json</code>. Symbols are the canonical entries. Click an entry to expand. Open PDF buttons go to canonical sources. For embedded prose snapshot with rendered math, open <code>CSR.snapshot.html</code> alongside this file.</div></details></span>')
    out.append('</div>')
    out.append('</header>')

    # Documents
    # Split documents into Document Registry (internal apparatus) and
    # Preprint Registry (external publications). Both render with the
    # same details/tag-row pattern as Symbol Registry.
    def _render_doc_entry(d):
        out.append(f'<details class="entry" data-id="{esc(d.id)}" id="{doc_anchor(d.id)}">')
        short_id = d.namespace or d.id.replace("csr.document.", "")
        out.append('<summary class="tag-row">')
        out.append(f'<span class="tag-id"><code>{esc(short_id)}</code></span>')
        out.append(f' {status_badge(d.status)}')
        out.append(f' <span class="tag-meta">{esc(d.version)} · {len(d.defines)} defines</span>')
        if d.display_name:
            preview = d.display_name[:90]
            if len(d.display_name) > 90:
                preview = preview.rstrip(" ,;:.-") + "…"
            out.append(f' <span class="tag-gloss">{esc(preview)}</span>')
        out.append(f' <span class="tag-action">{pdf_button(d.id, "PDF")}</span>')
        out.append(' <span class="tag-more">▾</span>')
        out.append('</summary>')
        out.append('<div class="entry-body">')
        out.append(f'<div class="entry-fullid"><code>{esc(d.id)}</code></div>')
        out.append('<table class="entry-table">')
        out.append(f'<tr><th style="width:13rem">Display</th><td>{esc(d.display_name)}</td></tr>')
        out.append(f'<tr><th>Version</th><td>{esc(d.version)}</td></tr>')
        out.append(f'<tr><th>Status</th><td>{status_badge(d.status)}</td></tr>')
        out.append(f'<tr><th>Publication mode</th><td>{esc(d.publication_mode)}</td></tr>')
        out.append(f'<tr><th>Last verified</th><td>{esc(d.last_verified)}</td></tr>')
        if d.defines:
            items = ", ".join(linkify_id(s) for s in d.defines)
            out.append(f'<tr><th>Defines ({len(d.defines)})</th><td>{items}</td></tr>')
        if d.depends_on:
            items = ", ".join(linkify_id(s) for s in d.depends_on)
            out.append(f'<tr><th>Depends on</th><td>{items}</td></tr>')
        out.append('</table>')
        out.append('</div>')
        out.append('</details>')

    internal_docs = sorted([d for d in reg.documents if (d.publication_mode or 'internal') != 'external'], key=lambda x: x.id)
    preprint_docs = sorted([d for d in reg.documents if d.publication_mode == 'external'], key=lambda x: x.id)

    # Recent additions / verifications. Combine documents and symbols by
    # last_verified date, descending. Top RECENT_LIMIT entries land at the
    # top of the page so the user can see what's new without scrolling.
    RECENT_LIMIT = 20
    recent_items = []
    for d in reg.documents:
        if d.last_verified:
            recent_items.append((d.last_verified, "doc", d))
    for s in reg.symbols:
        v = getattr(s, "verification", None)
        lv = getattr(v, "last_verified", "") if v else ""
        if lv:
            recent_items.append((lv, "sym", s))
    # Sort descending by date string (ISO YYYY-MM-DD sorts correctly as text),
    # then by id as a stable tiebreaker.
    recent_items.sort(key=lambda t: (t[0], getattr(t[2], "id", "")), reverse=True)
    recent_top = recent_items[:RECENT_LIMIT]
    if recent_top:
        out.append('<details class="section" id="recent" open>')
        out.append(f'<summary class="section-heading">Recent <span class="h2-count">(top {len(recent_top)})</span></summary>')
        out.append('<ul class="recent-list">')
        for date_str, kind, obj in recent_top:
            if kind == "doc":
                anchor = doc_anchor(obj.id)
                short = obj.id.replace("csr.document.", "")
                label = f"<code>{esc(short)}</code> <span class=\"recent-meta\">{esc(obj.display_name)} {esc(obj.version)}</span>"
                badge = status_badge(obj.status)
                kind_label = "doc"
            else:
                anchor = sym_anchor(obj.id)
                short = obj.id.split(".", 2)[-1] if obj.id.count(".") >= 2 else obj.id
                ns = obj.namespace
                label = f"<code>{esc(ns)}.{esc(short)}</code>"
                badge = status_badge(obj.status)
                kind_label = "sym"
            out.append(
                f'<li class="recent-item"><span class="recent-date">{esc(date_str)}</span> '
                f'<span class="recent-kind">{kind_label}</span> '
                f'<a href="#{anchor}">{label}</a> {badge}</li>'
            )
        out.append('</ul>')
        out.append('</details>')

    # Operator's Manual section. Two parts (agent-facing, human-facing) rendered
    # inline as collapsible details so they're discoverable from the viewer
    # without needing to open the .md files separately. Default collapsed.
    manuals = [
        ("manual-agent", "Operator's Manual, Part 1: Claude Cowork Agent",
         "CSR_Operators_Manual_Part1_Agent_v0.md"),
        ("manual-human", "Operator's Manual, Part 2: Human Operator",
         "CSR_Operators_Manual_Part2_Human_v0.md"),
    ]
    csr_root = Path(__file__).resolve().parent.parent
    for anchor, title, fname in manuals:
        manual_path = csr_root / fname
        if not manual_path.exists():
            continue
        md_text = manual_path.read_text(encoding="utf-8")
        out.append(f'<details class="section" id="{anchor}">')
        out.append(f'<summary class="section-heading">{esc(title)}</summary>')
        out.append('<div class="manual-body">')
        out.append(_render_minimal_markdown(md_text))
        out.append('</div>')
        out.append('</details>')

    out.append(f'<details class="section" id="document-registry">')
    out.append(f'<summary class="section-heading">Document Registry <span class="h2-count">({len(internal_docs)})</span></summary>')
    for d in internal_docs:
        _render_doc_entry(d)
    out.append('</details>')

    if preprint_docs:
        out.append(f'<details class="section" id="preprint-registry">')
        out.append(f'<summary class="section-heading">Preprint Registry <span class="h2-count">({len(preprint_docs)})</span></summary>')
        for d in preprint_docs:
            _render_doc_entry(d)
        out.append('</details>')

    # Symbols by namespace - salience-first (AestheticOperator §4):
    # ID + badge + definition + Open PDF at top; full metadata in collapsed
    # <details> below to keep V (visual density) bounded.
    out.append('<h2 id="symbol-registry">Symbol Registry</h2>')
    for ns in sorted(by_ns):
        ns_count = len(by_ns[ns])
        out.append(f'<details class="section section-ns" id="ns-{esc(ns)}">')
        out.append(f'<summary class="section-heading section-heading-ns"><code>{esc(ns)}</code> <span class="h2-count">({ns_count})</span></summary>')
        for s in sorted(by_ns[ns], key=lambda x: x.id):
            out.append(f'<details class="entry" data-namespace="{esc(ns)}" data-id="{esc(s.id)}" id="{sym_anchor(s.id)}">')
            short_id = s.id.replace("csr." + ns + ".", "")
            out.append('<summary class="tag-row">')
            out.append(f'<span class="tag-id"><code>{esc(short_id)}</code></span>')
            out.append(f' {status_badge(s.status)}')
            out.append(f' <span class="tag-meta">{esc(s.type)} · {esc(s.framework_layer)}</span>')
            if s.definition:
                preview = s.definition[:90]
                if len(s.definition) > 90:
                    preview = preview.rstrip(" ,;:.--") + "…"
                out.append(f' <span class="tag-gloss">{esc(preview)}</span>')
            if s.owning_document:
                out.append(f' <span class="tag-action">{pdf_button(s.owning_document, "PDF")}</span>')
            out.append(' <span class="tag-more">▾</span>')
            out.append('</summary>')
            out.append('<div class="entry-body">')
            # Full ID under the row (since we showed short)
            out.append(f'<div class="entry-fullid"><code>{esc(s.id)}</code></div>')
            # The gloss
            if s.definition:
                out.append(f'<p class="entry-gloss">{esc(s.definition)}</p>')
            out.append(f'<div class="entry-locator">Source: <code>{esc(s.definition_home)}</code></div>')
            out.append('<table class="entry-table">')
            out.append(f'<tr><th style="width:13rem">Display</th><td>{esc(s.display_name)}</td></tr>')
            out.append(f'<tr><th>Type</th><td>{esc(s.type)}</td></tr>')
            out.append(f'<tr><th>Framework layer</th><td><code>{esc(s.framework_layer)}</code></td></tr>')
            out.append(f'<tr><th>Owning document</th><td>{linkify_id(s.owning_document)}</td></tr>')
            short_h = (s.definition_hash[:14] + "...") if s.definition_hash and s.definition_hash.startswith("sha256:") else (s.definition_hash or "-")
            out.append(f'<tr><th>Definition hash</th><td><code>{esc(short_h)}</code></td></tr>')
            if s.applies_to:
                out.append(f'<tr><th>Applies to</th><td>{", ".join(esc(a) for a in s.applies_to)}</td></tr>')
            if s.components:
                out.append(f'<tr><th>Components</th><td>{", ".join(linkify_id(c) for c in s.components)}</td></tr>')
            if s.supersedes:
                out.append(f'<tr><th>Supersedes</th><td>{", ".join(linkify_id(c) for c in s.supersedes)}</td></tr>')
            if s.superseded_by:
                out.append(f'<tr><th>Superseded by</th><td>{", ".join(linkify_id(c) for c in s.superseded_by)}</td></tr>')
            rel_lines = []
            for rel in RELATION_TYPES:
                targets = getattr(s.relations, rel, [])
                if targets:
                    target_str = ", ".join(linkify_id(t) for t in targets)
                    rel_lines.append(f'<span class="rel-type">{esc(rel)}</span>: {target_str}')
            if rel_lines:
                out.append(f'<tr><th>Relations</th><td class="relations">{"<br>".join(rel_lines)}</td></tr>')
            v = s.verification
            out.append(f'<tr><th>Verification</th><td>{esc(v.state)} via {esc(v.method)}; last verified {esc(v.last_verified)}</td></tr>')
            out.append('</table>')
            out.append('</div>')  # /entry-body
            out.append('</details>')
        out.append('</details>')  # /section-ns

    # Collisions
    out.append('<h2 id="collisions">Known Collisions</h2>')
    for c in sorted(reg.collisions, key=lambda x: x.id):
        out.append(f'<h4>{esc(c.id)} {status_badge(c.status)}</h4>')
        out.append('<table>')
        out.append(f'<tr><th style="width:13rem">Resolution</th><td><code>{esc(c.resolution)}</code></td></tr>')
        if c.resolved_at:
            out.append(f'<tr><th>Resolved at</th><td>{esc(c.resolved_at)}</td></tr>')
        out.append(f'<tr><th>Owner</th><td>{esc(c.owner)}</td></tr>')
        if c.entries:
            items = "<br>".join(linkify_id(e) for e in c.entries)
            out.append(f'<tr><th>Entries</th><td>{items}</td></tr>')
        out.append('</table>')
        if c.resolution_note:
            out.append(f'<div class="def">{esc(c.resolution_note)}</div>')

    # Aliases
    out.append('<h2 id="aliases">Aliases</h2>')
    if reg.aliases:
        out.append('<table><tr><th>Alias</th><th>Resolves to</th></tr>')
        for a in sorted(reg.aliases, key=lambda x: x.source):
            out.append(f'<tr><td><code>{esc(a.source)}</code></td><td>{linkify_id(a.target)}</td></tr>')
        out.append('</table>')

    # Invariants
    out.append('<h2 id="invariants">Invariants</h2>')
    if reg.invariants:
        out.append('<table><tr><th>Invariant</th><th>Rule</th><th>Severity</th></tr>')
        for inv in sorted(reg.invariants, key=lambda x: x.name):
            out.append(f'<tr><td><code>{esc(inv.name)}</code></td><td>{esc(inv.rule)}</td><td>{esc(inv.severity)}</td></tr>')
        out.append('</table>')

    out.append('</main></div>')
    out.append(f'<script>{js}</script>')
    out.append('</body></html>')
    return "\n".join(out)


def render_wiki_html(reg, compiled_at, errors, warnings, svg_inline=""):
    # Source-prose extraction (Live Wiki feature). Cache parses to avoid
    # re-walking each .tex file once per symbol.
    _src_cache = None
    if csr_extract is not None:
        try:
            _src_cache = csr_extract.SourceCache(Path(__file__).resolve().parent.parent)
        except Exception:
            _src_cache = None

    import html as _html

    canonical_syms = sum(1 for s in reg.symbols if s.status == "canonical")
    candidate_syms = sum(1 for s in reg.symbols if s.status == "candidate")
    canonical_docs = sum(1 for d in reg.documents if d.status == "canonical")
    candidate_docs = sum(1 for d in reg.documents if d.status == "candidate")

    # Build set of known IDs for cross-reference linkification
    known_symbol_ids = {s.id for s in reg.symbols}
    known_document_ids = {d.id for d in reg.documents}

    def esc(s):
        return _html.escape(str(s)) if s is not None else ""

    def status_badge(status):
        return f'<span class="badge {esc(status)}">{esc(status)}</span>'

    def sym_anchor(sid):
        return "sym-" + re.sub(r"[^A-Za-z0-9]", "-", sid)

    def doc_anchor(did):
        return "doc-" + re.sub(r"[^A-Za-z0-9]", "-", did)

    def linkify_id(token):
        """If token is a known symbol or document ID, return a link to its anchor.
        Otherwise return as escaped code."""
        token = token.strip()
        if token in known_symbol_ids:
            return f'<a class="xref" href="#{sym_anchor(token)}"><code>{esc(token)}</code></a>'
        if token in known_document_ids:
            return f'<a class="xref" href="#{doc_anchor(token)}"><code>{esc(token)}</code></a>'
        return f'<code>{esc(token)}</code>'

    css = """
:root {
  /* Color (dark mode default) */
  --bg: #14171a; --fg: #e8e8e8; --muted: #8a8e96; --border: #2c3038;
  --code-bg: #1d2025; --accent: #5fa66a; --warn: #f0a02b; --err: #ef6464;
  --sidebar-bg: #1a1d22; --tint-hover: rgba(95, 166, 106, 0.10);
  --tint-open: rgba(95, 166, 106, 0.16); --tint-scroll: rgba(255,255,255,0.16);
  --tint-scroll-hover: rgba(255,255,255,0.30);
  --canonical-bg: #1a3d27; --canonical-fg: #b6e6c4;
  --candidate-bg: #463a10; --candidate-fg: #ffe89e;
  --provisional-bg: #1e4030; --provisional-fg: #b9f0c9;
  --deprecated-bg: #2a2c30; --deprecated-fg: #b0b0b0;
  --rejected-bg: #4a1d1d; --rejected-fg: #ffb3b3;
  --deferred-bg: #2e1d52; --deferred-fg: #d6c2ff;
  --draft-bg: #1a1d22; --draft-fg: #b0b0b0;
  --resolved-bg: #1e4030; --resolved-fg: #b9f0c9;

  /* Type: golden minor (sqrt phi = 1.272) from 14px base */
  --fs-xs: 0.78rem; --fs-sm: 0.88rem; --fs-md: 0.94rem; --fs-base: 1rem;
  --fs-h3: 1.272rem; --fs-h2: 1.618rem; --fs-h1: 2.058rem;

  /* Space: 1.5x rhythm; sp-6/sp-7 expand to phi^2 phi^3 for major breaks */
  --sp-1: 0.25rem; --sp-2: 0.5rem; --sp-3: 0.75rem; --sp-4: 1rem;
  --sp-5: 1.5rem; --sp-6: 2.5rem; --sp-7: 4rem;

  /* Layout: sidebar : content = 1 : phi^2 */
  --sidebar-w: 14rem; --content-max: 54rem;
  --radius: 3px; --radius-pill: 999px;
}
* { box-sizing: border-box; }
body {
  margin: 0; font-family: -apple-system, "Segoe UI", Roboto, "Helvetica Neue", sans-serif;
  font-size: 14px; line-height: 1.55; color: var(--fg); background: var(--bg);
  font-feature-settings: "kern" 1, "liga" 1;
}

/* Layout: sidebar is the only architectural column boundary */
.layout { display: flex; min-height: 100vh; }
.sidebar {
  width: var(--sidebar-w); flex-shrink: 0;
  background: var(--sidebar-bg); border-right: 1px solid var(--border);
  position: sticky; top: 0; height: 100vh; overflow-y: auto;
  padding: var(--sp-5) var(--sp-4); font-size: var(--fs-sm);
  scrollbar-width: thin;
  scrollbar-color: var(--tint-scroll) transparent;
}
.sidebar::-webkit-scrollbar { width: 5px; }
.sidebar::-webkit-scrollbar-track { background: transparent; }
.sidebar::-webkit-scrollbar-thumb { background: var(--tint-scroll); border-radius: var(--radius); }
.sidebar::-webkit-scrollbar-thumb:hover { background: var(--tint-scroll-hover); }
.sidebar h2 {
  font-size: var(--fs-sm); margin-top: var(--sp-5); margin-bottom: var(--sp-2);
  color: var(--accent); border: none; padding: 0; font-weight: 600;
  text-transform: uppercase; letter-spacing: 0.05em;
}
.sidebar h2:first-child { margin-top: 0; }
.sidebar ul { list-style: none; margin: 0; padding-left: var(--sp-3); }
.sidebar li { margin: var(--sp-1) 0; }
.sidebar a { color: var(--fg); text-decoration: none; word-break: break-word; }
.sidebar a:hover { color: var(--accent); }
.sidebar .ns-group, .sidebar .doc-group { margin-bottom: var(--sp-2); }
/* Main-content section collapsibles: Document Registry, Preprint Registry, each Namespace */
details.section { margin: var(--sp-5) 0 var(--sp-3) 0; border-top: 1px solid var(--border); padding-top: var(--sp-3); }
details.section[open] { margin-bottom: var(--sp-5); }
summary.section-heading {
  cursor: pointer; list-style: none;
  font-size: var(--fs-h2); font-weight: 600; line-height: 1.25;
  padding: var(--sp-2) 0; color: var(--fg);
  display: flex; align-items: baseline; gap: var(--sp-2);
}
summary.section-heading::-webkit-details-marker { display: none; }
summary.section-heading::before {
  content: "\\25B8"; font-size: 0.7em; transition: transform 0.15s; color: var(--muted); flex-shrink: 0;
}
details.section[open] > summary.section-heading::before { transform: rotate(90deg); color: var(--accent); }
summary.section-heading:hover { color: var(--accent); }
summary.section-heading-ns { font-size: var(--fs-h3); }
summary.section-heading .h2-count { font-size: var(--fs-base); color: var(--muted); font-weight: 400; }
details.section section.section-body { padding-left: 0; }
.manual-body { padding: var(--sp-2) 0 var(--sp-3) 0; max-width: 56rem; }
.manual-body h2.manual-h2 { font-size: var(--fs-h3); margin: var(--sp-4) 0 var(--sp-2) 0; border: none; padding: 0; }
.manual-body h3.manual-h3 { font-size: var(--fs-base); font-weight: 600; margin: var(--sp-3) 0 var(--sp-1) 0; color: var(--accent); border: none; padding: 0; }
.manual-body h4.manual-h4 { font-size: var(--fs-base); font-weight: 600; margin: var(--sp-2) 0 var(--sp-1) 0; color: var(--fg); border: none; padding: 0; }
.manual-body p { margin: var(--sp-2) 0; line-height: 1.55; }
.manual-body pre.manual-code {
  background: var(--sidebar-bg); border-left: 2px solid var(--accent);
  padding: var(--sp-2) var(--sp-3); margin: var(--sp-2) 0;
  overflow-x: auto; font-size: var(--fs-sm); line-height: 1.45;
}
.manual-body pre.manual-code code { background: transparent; padding: 0; color: var(--fg); }
ul.recent-list { list-style: none; padding-left: 0; margin: var(--sp-2) 0; }
li.recent-item { padding: var(--sp-1) 0; font-size: var(--fs-sm); display: flex; flex-wrap: wrap; align-items: baseline; gap: var(--sp-2); border-bottom: 1px solid var(--border); }
li.recent-item:last-child { border-bottom: none; }
li.recent-item .recent-date { color: var(--muted); font-variant-numeric: tabular-nums; flex-shrink: 0; }
li.recent-item .recent-kind { color: var(--muted); font-size: var(--fs-xs); text-transform: uppercase; letter-spacing: 0.05em; flex-shrink: 0; min-width: 2.5rem; }
li.recent-item .recent-meta { color: var(--muted); font-weight: 400; }
li.recent-item a { color: var(--fg); text-decoration: none; }
li.recent-item a:hover { color: var(--accent); }
.sidebar .ns-label {
  font-weight: 600; color: var(--muted); font-size: var(--fs-xs);
  text-transform: uppercase; letter-spacing: 0.05em; margin-top: var(--sp-2);
  cursor: pointer; list-style: none; padding: var(--sp-1) 0;
  display: flex; align-items: center; gap: var(--sp-2);
}
.sidebar .ns-label::-webkit-details-marker { display: none; }
.sidebar .ns-label::before {
  content: "\\25B8"; font-size: 0.7em; transition: transform 0.15s; color: var(--muted);
}
.sidebar details[open] > .ns-label::before { transform: rotate(90deg); }
.sidebar .ns-label:hover { color: var(--accent); }
.sidebar details[open] > .ns-label { color: var(--fg); }
.sidebar .filter {
  width: 100%; padding: var(--sp-2) var(--sp-2); margin-bottom: var(--sp-4); font-size: var(--fs-sm);
  border: none; border-bottom: 1px solid var(--border); background: transparent;
  border-radius: 0; font-family: inherit; outline: none;
}
.sidebar .filter:focus { border-bottom-color: var(--accent); }

.content {
  flex: 1; padding: var(--sp-5) var(--sp-5) var(--sp-6) var(--sp-5);
  max-width: var(--content-max); margin: 0 auto;
}

/* Page header: compact single-band with build ticker */
.page-head { margin-bottom: var(--sp-5); padding-bottom: var(--sp-3); border-bottom: 1px solid var(--border); }
.page-head h1 { margin: 0 0 var(--sp-2) 0; border: none; padding: 0; font-size: var(--fs-h2); }
.ticker { display: flex; flex-wrap: wrap; gap: var(--sp-4); align-items: baseline; font-size: var(--fs-sm); color: var(--muted); }
.ticker b { color: var(--fg); font-weight: 600; }
.ticker-tail { margin-left: auto; opacity: 0.7; }
.ticker-help { display: inline-block; }
.ticker-help summary { cursor: pointer; list-style: none; padding: 0 var(--sp-1); border-radius: var(--radius); color: var(--muted); }
.ticker-help summary::-webkit-details-marker { display: none; }
.ticker-help summary:hover { color: var(--accent); }
.ticker-help-body { position: absolute; right: var(--sp-5); margin-top: var(--sp-2); max-width: 28rem; padding: var(--sp-3); background: var(--code-bg); border: 1px solid var(--border); border-radius: var(--radius); font-style: normal; color: var(--fg); z-index: 50; }

/* Type rhythm: only h1 / h2 carry baseline rules; everything else uses space */
h1 {
  font-size: var(--fs-h1); margin-top: 0;
  border-bottom: 1px solid var(--fg); padding-bottom: var(--sp-2);
  line-height: 1.2; font-weight: 600; letter-spacing: -0.01em;
}
.h2-count { font-size: var(--fs-sm); color: var(--muted); font-weight: 400; margin-left: var(--sp-2); letter-spacing: normal; }
h2 {
  font-size: var(--fs-h2); margin-top: var(--sp-7); padding-bottom: var(--sp-1);
  border-bottom: 1px solid var(--border); line-height: 1.3; font-weight: 600;
}
h3 {
  font-size: var(--fs-h3); margin-top: var(--sp-6); color: var(--accent);
  line-height: 1.35; font-weight: 600;
}
h4 {
  font-size: var(--fs-base); margin-top: var(--sp-5); padding-top: var(--sp-1);
  font-family: ui-monospace, "SF Mono", Consolas, monospace;
  scroll-margin-top: var(--sp-3); font-weight: 600;
}
h4 .anchor-link {
  font-size: var(--fs-xs); color: var(--muted); text-decoration: none;
  margin-left: var(--sp-2); opacity: 0; transition: opacity 0.15s;
}
h4:hover .anchor-link { opacity: 1; }

/* Code: faint background only, no frame */
code, pre { font-family: ui-monospace, "SF Mono", Consolas, "Menlo", monospace; font-size: 0.92em; }
code { background: var(--code-bg); padding: 0.1em 0.35em; border-radius: var(--radius); }
pre { background: var(--code-bg); padding: var(--sp-3) var(--sp-4); border-radius: var(--radius); overflow-x: auto; border: none; }

.muted { color: var(--muted); font-style: italic; }
.preamble { font-size: var(--fs-sm); color: var(--muted); margin: 0 0 var(--sp-5) 0; }

/* Tables: only header underline, no per-cell grid (tables are not data prisons) */
table { border-collapse: collapse; width: 100%; margin: var(--sp-3) 0 var(--sp-5) 0; font-size: var(--fs-sm); }
th, td { border: none; padding: var(--sp-2) var(--sp-3) var(--sp-2) 0; text-align: left; vertical-align: top; }
th { font-weight: 600; color: var(--muted); font-size: var(--fs-xs); text-transform: uppercase; letter-spacing: 0.05em; border-bottom: 1px solid var(--border); }

/* Status badges: the badge IS the boundary, keep its edges */
.badge { display: inline-block; padding: 0.05rem 0.55rem; border-radius: var(--radius-pill); font-size: var(--fs-xs); font-weight: 600; vertical-align: middle; letter-spacing: 0.02em; }
.badge.canonical    { background: var(--canonical-bg);    color: var(--canonical-fg); }
.badge.candidate    { background: var(--candidate-bg);    color: var(--candidate-fg); }
.badge.provisional  { background: var(--provisional-bg);  color: var(--provisional-fg); }
.badge.deprecated   { background: var(--deprecated-bg);   color: var(--deprecated-fg); }
.badge.rejected     { background: var(--rejected-bg);     color: var(--rejected-fg); }
.badge.deferred     { background: var(--deferred-bg);     color: var(--deferred-fg); }
.badge.draft        { background: var(--draft-bg);        color: var(--draft-fg); }
.badge.resolved     { background: var(--resolved-bg);     color: var(--resolved-fg); }

/* Metrics, definitions, relations: text-only, no frames */
.metric { display: inline-block; margin-right: var(--sp-5); }
.metric .v { font-weight: 700; font-size: var(--fs-h3); }
.metric .l { color: var(--muted); font-size: var(--fs-sm); margin-left: var(--sp-1); }
.def { color: var(--muted); padding: 0; margin: var(--sp-2) 0 var(--sp-4) 0; font-size: var(--fs-md); font-style: italic; }
.relations { font-size: var(--fs-md); }
.relations .rel-type { font-weight: 600; color: var(--accent); }
a.xref { text-decoration: none; }
a.xref code { color: var(--accent); }
a.xref:hover code { background: var(--canonical-bg); }
a.pdf-link {
  display: inline-block; padding: var(--sp-1) var(--sp-3); background: var(--canonical-bg);
  color: var(--canonical-fg); border-radius: var(--radius); text-decoration: none;
  font-size: var(--fs-sm); font-weight: 600;
}
a.pdf-link:hover { background: var(--accent); color: #fff; }
.pdf-link.unavailable { color: var(--muted); font-size: var(--fs-sm); background: transparent; padding: var(--sp-1) 0; }

/* Graph and notes: no frames, just space */
.graph-wrap { border: none; padding: 0; background: transparent; overflow: auto; margin: var(--sp-5) 0 var(--sp-6) 0; text-align: center; }
.graph-wrap svg { display: inline-block; max-width: 100%; height: auto; }
.print-note { background: transparent; border-left: 2px solid var(--accent); padding: 0 var(--sp-4); margin: var(--sp-4) 0; font-size: var(--fs-md); color: var(--muted); font-style: italic; }

/* Source prose: typographic only, no boxed callouts */
.source-prose { padding: 0; margin: var(--sp-3) 0 var(--sp-5) 0; font-size: var(--fs-md); }
.source-prose p { margin: 0.5em 0; }
.source-prose .source-header {
  font-weight: 600; color: var(--accent); margin: var(--sp-3) 0 var(--sp-2) 0;
  font-size: var(--fs-xs); text-transform: uppercase; letter-spacing: 0.06em;
}
.source-prose blockquote { border-left: 2px solid var(--border); padding-left: var(--sp-3); color: var(--muted); margin: var(--sp-3) 0; }
.source-prose .math.inline, .source-prose .math.display { font-size: 1em; }
.source-prose .katex-display { margin: 0.6em 0; }
.source-prose .katex { font-size: 1.05em; }
.source-prose br { content: ""; display: block; margin-top: 0.35em; }
.source-prose p strong + em { color: var(--accent); }
.source-prose p strong:first-child { display: inline-block; min-width: 1.5em; }
/* Theorem-like environments: italic header pattern, no surrounding box */
.source-prose .definition, .source-prose .theorem, .source-prose .proposition {
  background: transparent; border: none; padding: 0; margin: var(--sp-3) 0; font-size: var(--fs-md);
}

@media print {
  .sidebar { display: none; }
  .content { padding: 0.6in; max-width: none; font-size: 11pt; }
  h2 { page-break-after: avoid; }
  h3, h4 { page-break-after: avoid; }
  table, .graph-wrap, .def, .source-prose { page-break-inside: avoid; }
  .print-note { display: none; }
  a { color: var(--fg); text-decoration: none; }
}
@media (max-width: 900px) {
  .sidebar { display: none; }
  .content { padding: var(--sp-4); }
}
"""

    js = """
(function() {
  // Filter: hide TOC entries that don't match the input.
  var input = document.getElementById('toc-filter');
  if (!input) return;
  input.addEventListener('input', function() {
    var q = this.value.trim().toLowerCase();
    document.querySelectorAll('.sidebar li[data-id]').forEach(function(li) {
      var id = li.getAttribute('data-id').toLowerCase();
      li.style.display = (q === '' || id.indexOf(q) !== -1) ? '' : 'none';
    });
    // Hide ns-groups whose visible children are zero
    document.querySelectorAll('.sidebar .ns-group').forEach(function(g) {
      var visible = g.querySelectorAll('li[data-id]:not([style*="display: none"])').length;
      g.style.display = visible > 0 ? '' : 'none';
    });
  });
})();
"""

    # MathJax config: also accept $...$ inline so older content works
    mathjax = """
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/contrib/auto-render.min.js"
        onload="renderMathInElement(document.body, {
          delimiters: [
            {left: '$$', right: '$$', display: true},
            {left: '\\\\[', right: '\\\\]', display: true},
            {left: '$', right: '$', display: false},
            {left: '\\\\(', right: '\\\\)', display: false}
          ],
          throwOnError: false,
          ignoredTags: ['script', 'noscript', 'style', 'textarea', 'pre', 'code']
        });"></script>
"""

    # Group symbols and documents for the sidebar TOC
    by_ns = {}
    for s in reg.symbols:
        by_ns.setdefault(s.namespace or "_unknown", []).append(s)

    # Build TOC HTML
    toc_lines = []
    toc_lines.append('<input class="filter" id="toc-filter" placeholder="Filter symbols..." />')
    toc_lines.append('<h2>Sections</h2><ul>')
    # build-state moved into compact header; no separate TOC link
    toc_lines.append('<li><a href="#migration">Migration</a></li>')
    if svg_inline:
        toc_lines.append('<li><a href="#dependency-graph">Dependency graph</a></li>')
    toc_lines.append('<li><a href="#document-registry">Document Registry</a></li>')
    toc_lines.append('<li><a href="#preprint-registry">Preprint Registry</a></li>')
    toc_lines.append('<li><a href="#symbol-registry">Symbol Registry</a></li>')
    toc_lines.append('<li><a href="#collisions">Known Collisions</a></li>')
    toc_lines.append('<li><a href="#aliases">Aliases</a></li>')
    toc_lines.append('<li><a href="#invariants">Invariants</a></li>')
    toc_lines.append('</ul>')
    toc_lines.append('<h2>Symbols by namespace</h2>')
    for ns in sorted(by_ns):
        toc_lines.append(f'<details class="ns-group" data-ns="{esc(ns)}">')
        toc_lines.append(f'<summary class="ns-label">{esc(ns)}</summary>')
        toc_lines.append('<ul>')
        for s in sorted(by_ns[ns], key=lambda x: x.id):
            toc_lines.append(
                f'<li data-id="{esc(s.id)}"><a href="#{sym_anchor(s.id)}">'
                f'<code>{esc(s.id.replace("csr." + ns + ".", ""))}</code></a></li>'
            )
        toc_lines.append('</ul>')
        toc_lines.append('</details>')
    toc_lines.append('<details class="doc-group"><summary class="ns-label">Documents</summary><ul>')
    for d in sorted(reg.documents, key=lambda x: x.id):
        short = d.id.replace("csr.document.", "")
        toc_lines.append(
            f'<li data-id="{esc(d.id)}"><a href="#{doc_anchor(d.id)}">'
            f'<code>{esc(short)}</code></a></li>'
        )
    toc_lines.append('</ul></details>')

    out = []
    out.append("<!DOCTYPE html>")
    out.append('<html lang="en"><head><meta charset="utf-8">')
    out.append("<title>CSR Live View</title>")
    out.append(f"<style>{css}</style>")
    out.append(mathjax)
    out.append("</head><body>")
    out.append('<div class="layout">')
    out.append('<aside class="sidebar">')
    out.extend(toc_lines)
    out.append('</aside>')

    out.append('<main class="content">')
    out.append('<h1>Corpus Semantic Registry: Live View</h1>')
    out.append('<div class="preamble">')
    out.append('Rendered output of <code>build/CSR.lock.json</code>. Non-authoritative. ')
    out.append(f'Source of truth: <code>.csr</code> files in <code>registry/</code>. Compiled at: {esc(compiled_at)}. ')
    out.append('Each symbol entry shows registry metadata followed by canonical prose extracted from the source document.')
    out.append('</div>')

    out.append('<div class="print-note">')
    out.append('To save as PDF: press <strong>Ctrl-P</strong> in the browser and choose <strong>Save as PDF</strong>. ')
    out.append('Math is rendered live by MathJax; cross-references navigate within the page.')
    out.append('</div>')

    # Build state
    out.append('<h2 id="build-state">Build state</h2>')
    out.append('<div>')
    err_color = "var(--err)" if errors else "inherit"
    warn_color = "var(--warn)" if warnings else "inherit"
    out.append(f'<span class="metric"><span class="v" style="color:{err_color}">{errors}</span><span class="l">errors</span></span>')
    out.append(f'<span class="metric"><span class="v" style="color:{warn_color}">{warnings}</span><span class="l">warnings</span></span>')
    out.append(f'<span class="metric"><span class="v">{len(reg.symbols)}</span><span class="l">symbols ({canonical_syms} canonical, {candidate_syms} candidate)</span></span>')
    out.append(f'<span class="metric"><span class="v">{len(reg.documents)}</span><span class="l">documents</span></span>')
    out.append(f'<span class="metric"><span class="v">{len(reg.collisions)}</span><span class="l">collisions</span></span>')
    out.append('</div>')

    # Migration
    out.append('<h2 id="migration">Migration</h2>')
    for m in sorted(reg.migrations, key=lambda x: x.name):
        out.append(f'<h3>{esc(m.name)}</h3>')
        out.append('<table>')
        out.append(f'<tr><th style="width:14rem">From</th><td>{esc(m.from_)}</td></tr>')
        out.append(f'<tr><th>To</th><td>{esc(m.to)}</td></tr>')
        out.append(f'<tr><th>Target wiki version</th><td>{esc(m.target_wiki_version)}</td></tr>')
        out.append(f'<tr><th>Status</th><td>{status_badge(m.status)}</td></tr>')
        out.append(f'<tr><th>Decision</th><td>{esc(m.decision)}</td></tr>')
        if m.replaces:
            items = ", ".join(f"<code>{esc(r)}</code>" for r in m.replaces)
            out.append(f'<tr><th>Replaces</th><td>{items}</td></tr>')
        if m.renders:
            items = "<br>".join(f"<code>{esc(r)}</code>" for r in m.renders)
            out.append(f'<tr><th>Renders</th><td>{items}</td></tr>')
        if m.preserves:
            items = "<br>".join(f"<code>{esc(r)}</code>" for r in m.preserves)
            out.append(f'<tr><th>Preserves</th><td>{items}</td></tr>')
        out.append('</table>')

    # Dependency graph (embedded SVG)
    if svg_inline:
        out.append('<h2 id="dependency-graph">Dependency graph</h2>')
        out.append('<div class="graph-wrap">')
        out.append(svg_inline)
        out.append('</div>')

    # Documents
    out.append('<h2 id="document-registry">Document Registry</h2>')
    for d in sorted(reg.documents, key=lambda x: x.id):
        out.append(f'<h4 id="{doc_anchor(d.id)}">{esc(d.id)} {status_badge(d.status)}'
                   f'<a class="anchor-link" href="#{doc_anchor(d.id)}">¶</a></h4>')
        out.append('<table>')
        out.append(f'<tr><th style="width:13rem">Display</th><td>{esc(d.display_name)}</td></tr>')
        out.append(f'<tr><th>Version</th><td>{esc(d.version)}</td></tr>')
        out.append(f'<tr><th>Namespace</th><td><code>{esc(d.namespace)}</code></td></tr>')
        out.append(f'<tr><th>Publication</th><td>{esc(d.publication_mode)}</td></tr>')
        out.append(f'<tr><th>Last verified</th><td>{esc(d.last_verified)}</td></tr>')
        if d.defines:
            items = ", ".join(linkify_id(x) for x in d.defines)
            out.append(f'<tr><th>Defines</th><td>{items}</td></tr>')
        if d.depends_on:
            items = ", ".join(linkify_id(x) for x in d.depends_on)
            out.append(f'<tr><th>Depends on</th><td>{items}</td></tr>')
        out.append('</table>')

    # Symbols by namespace
    out.append('<h2 id="symbol-registry">Symbol Registry</h2>')
    for ns in sorted(by_ns):
        out.append(f'<h3>Namespace: <code>{esc(ns)}</code></h3>')
        for s in sorted(by_ns[ns], key=lambda x: x.id):
            out.append(f'<h4 id="{sym_anchor(s.id)}">{esc(s.id)} {status_badge(s.status)}'
                       f'<a class="anchor-link" href="#{sym_anchor(s.id)}">¶</a></h4>')
            out.append('<table>')
            out.append(f'<tr><th style="width:13rem">Display</th><td>{esc(s.display_name)}</td></tr>')
            out.append(f'<tr><th>Type</th><td>{esc(s.type)}</td></tr>')
            out.append(f'<tr><th>Framework layer</th><td><code>{esc(s.framework_layer)}</code></td></tr>')
            out.append(f'<tr><th>Owning document</th><td>{linkify_id(s.owning_document)}</td></tr>')
            out.append(f'<tr><th>Definition home</th><td><code>{esc(s.definition_home)}</code></td></tr>')
            short_h = (s.definition_hash[:14] + "...") if s.definition_hash and s.definition_hash.startswith("sha256:") else (s.definition_hash or "-")
            out.append(f'<tr><th>Definition hash</th><td><code>{esc(short_h)}</code></td></tr>')
            if s.applies_to:
                out.append(f'<tr><th>Applies to</th><td>{", ".join(esc(a) for a in s.applies_to)}</td></tr>')
            if s.components:
                out.append(f'<tr><th>Components</th><td>{", ".join(linkify_id(c) for c in s.components)}</td></tr>')
            if s.supersedes:
                out.append(f'<tr><th>Supersedes</th><td>{", ".join(linkify_id(c) for c in s.supersedes)}</td></tr>')
            if s.superseded_by:
                out.append(f'<tr><th>Superseded by</th><td>{", ".join(linkify_id(c) for c in s.superseded_by)}</td></tr>')
            rel_lines = []
            for rel in RELATION_TYPES:
                targets = getattr(s.relations, rel, [])
                if targets:
                    target_str = ", ".join(linkify_id(t) for t in targets)
                    rel_lines.append(f'<span class="rel-type">{esc(rel)}</span>: {target_str}')
            if rel_lines:
                out.append(f'<tr><th>Relations</th><td class="relations">{"<br>".join(rel_lines)}</td></tr>')
            v = s.verification
            out.append(f'<tr><th>Verification</th><td>{esc(v.state)} via {esc(v.method)}; last verified {esc(v.last_verified)}</td></tr>')
            out.append('</table>')
            out.append(f'<div class="def">{esc(s.definition)}</div>')

            # Inline source-document prose
            if csr_extract is not None and _src_cache is not None and s.definition_home:
                try:
                    prose = csr_extract.extract_for_locator(_src_cache, s.definition_home)
                    if prose:
                        out.append(prose)
                except Exception:
                    pass

    # Collisions
    out.append('<h2 id="collisions">Known Collisions</h2>')
    for c in sorted(reg.collisions, key=lambda x: x.id):
        out.append(f'<h4>{esc(c.id)} {status_badge(c.status)}</h4>')
        out.append('<table>')
        out.append(f'<tr><th style="width:13rem">Resolution</th><td><code>{esc(c.resolution)}</code></td></tr>')
        if c.resolved_at:
            out.append(f'<tr><th>Resolved at</th><td>{esc(c.resolved_at)}</td></tr>')
        out.append(f'<tr><th>Owner</th><td>{esc(c.owner)}</td></tr>')
        out.append(f'<tr><th>Last verified</th><td>{esc(c.last_verified)}</td></tr>')
        if c.entries:
            items = "<br>".join(linkify_id(e) for e in c.entries)
            out.append(f'<tr><th>Entries</th><td>{items}</td></tr>')
        out.append('</table>')
        if c.resolution_note:
            out.append(f'<div class="def">{esc(c.resolution_note)}</div>')

    # Aliases
    out.append('<h2 id="aliases">Aliases</h2>')
    if reg.aliases:
        out.append('<table>')
        out.append('<tr><th>Alias</th><th>Resolves to</th></tr>')
        for a in sorted(reg.aliases, key=lambda x: x.source):
            out.append(f'<tr><td><code>{esc(a.source)}</code></td><td>{linkify_id(a.target)}</td></tr>')
        out.append('</table>')
    else:
        out.append('<p class="muted">(none)</p>')

    # Invariants
    out.append('<h2 id="invariants">Invariants</h2>')
    if reg.invariants:
        out.append('<table>')
        out.append('<tr><th>Invariant</th><th>Rule</th><th>Severity</th></tr>')
        for inv in sorted(reg.invariants, key=lambda x: x.name):
            out.append(f'<tr><td><code>{esc(inv.name)}</code></td><td>{esc(inv.rule)}</td><td>{esc(inv.severity)}</td></tr>')
        out.append('</table>')

    out.append('<hr>')
    out.append(f'<p class="muted">End of live view. Regenerate by double-clicking BUILD.bat or running <code>csr build</code>.</p>')
    out.append('</main>')
    out.append('</div>')  # /layout
    out.append(f"<script>{js}</script>")
    out.append('</body></html>')
    return "\n".join(out)




# ----------------------------------------------------------------------------
# Wiki-style consolidated registry auto-emitter (LaTeX output)
# ----------------------------------------------------------------------------

def _tex_escape(s):
    if not s: return ""
    s = s.replace("\\", "\\textbackslash{}")
    s = s.replace("&", "\\&").replace("%", "\\%").replace("$", "\\$")
    s = s.replace("#", "\\#").replace("_", "\\_").replace("^", "\\^{}")
    s = s.replace("{", "\\{").replace("}", "\\}")
    s = s.replace("~", "\\textasciitilde{}")
    return s


def render_consolidated_doc_registry(reg, compiled_at):
    BS = chr(92)
    NL = chr(10)
    lines = []
    lines.append("% Document Registry - auto-generated from CSR.lock.json")
    lines.append("% Compiled at: " + compiled_at)
    lines.append("% DO NOT EDIT MANUALLY. Regenerate via: python tools/csr.py build")
    lines.append("")
    internal = sorted([d for d in reg.documents if (d.publication_mode or "internal") != "external"], key=lambda x: x.id)
    preprints = sorted([d for d in reg.documents if d.publication_mode == "external"], key=lambda x: x.id)

    def row(d):
        ns = d.namespace or d.id.replace("csr.document.", "")
        r = []
        r.append(BS + "noindent" + BS + "textbf{" + _tex_escape(ns) + "}" + BS + "hfill" + BS + "texttt{" + _tex_escape(d.status) + "}" + BS + BS)
        r.append(BS + "textit{display:} " + _tex_escape(d.display_name) + BS + BS)
        r.append(BS + "textit{current" + BS + "_version:} " + _tex_escape(d.version) + BS + BS)
        r.append(BS + "textit{publication" + BS + "_mode:} " + _tex_escape(d.publication_mode) + BS + BS)
        r.append(BS + "textit{last" + BS + "_verified:} " + _tex_escape(d.last_verified))
        if d.defines:
            short = ", ".join(t.split(".")[-1] for t in d.defines[:6])
            if len(d.defines) > 6:
                short += ", ...(" + str(len(d.defines)) + " total)"
            r.append(BS + BS + BS + "textit{defines:} " + _tex_escape(short))
        if d.depends_on:
            short = ", ".join(t.split(".")[-1] for t in d.depends_on[:6])
            if len(d.depends_on) > 6:
                short += ", ...(" + str(len(d.depends_on)) + " total)"
            r.append(BS + BS + BS + "textit{depends" + BS + "_on:} " + _tex_escape(short))
        r.append(BS + "par" + BS + "smallskip")
        return NL.join(r)

    lines.append(BS + "subsubsection*{Internal documents (" + str(len(internal)) + ")}")
    lines.append(BS + "begin{multicols}{2}" + BS + "footnotesize")
    lines.append("")
    for d in internal:
        lines.append(row(d))
        lines.append("")
    lines.append(BS + "end{multicols}")
    lines.append("")
    if preprints:
        lines.append(BS + "subsubsection*{External publications / preprints (" + str(len(preprints)) + ")}")
        lines.append(BS + "begin{multicols}{2}" + BS + "footnotesize")
        lines.append("")
        for d in preprints:
            lines.append(row(d))
            lines.append("")
        lines.append(BS + "end{multicols}")
    return NL.join(lines) + NL


def render_consolidated_symbol_registry(reg, compiled_at):
    BS = chr(92)
    NL = chr(10)
    lines = []
    lines.append("% Symbol Registry - auto-generated from CSR.lock.json")
    lines.append("% Compiled at: " + compiled_at)
    lines.append("% DO NOT EDIT MANUALLY. Regenerate via: python tools/csr.py build")
    lines.append("")
    by_ns = {}
    for s in reg.symbols:
        by_ns.setdefault(s.namespace or "_unknown", []).append(s)
    canon = sum(1 for s in reg.symbols if s.status == "canonical")
    cand = sum(1 for s in reg.symbols if s.status == "candidate")
    lines.append(BS + "noindent" + BS + "textit{" + str(len(reg.symbols)) + " symbols across " + str(len(by_ns)) + " namespaces.}")
    lines.append(BS + "textit{Canonical: " + str(canon) + "; candidate: " + str(cand) + ".}")
    lines.append("")
    lines.append(BS + "begin{multicols}{2}" + BS + "scriptsize")
    lines.append("")
    for ns in sorted(by_ns):
        lines.append(BS + "noindent" + BS + "textbf{" + _tex_escape(ns) + "} " + BS + "textit{(" + str(len(by_ns[ns])) + " entries)}" + BS + BS)
        for s in sorted(by_ns[ns], key=lambda x: x.id):
            short_id = s.id.replace("csr." + ns + ".", "").replace("csr.", "")
            line_text = BS + "texttt{" + _tex_escape(short_id) + "} " + BS + "textit{" + _tex_escape(s.type or "-") + "} " + _tex_escape(s.status)
            lines.append(BS + "noindent" + BS + "hangindent=1em " + line_text + BS + BS)
        lines.append(BS + "par" + BS + "smallskip")
        lines.append("")
    lines.append(BS + "end{multicols}")
    return NL.join(lines) + NL



def render_doc_footer(doc, reg, compiled_at: str) -> str:
    """Generate the canonical footer block for one document.
    Authors paste this at the end of their source. Regenerated on every CSR
    build so dependency / defines lists stay current."""
    deps = sorted(set(doc.depends_on))
    defines = sorted(set(doc.defines))[:24]  # cap; full list in CSR.lock.json
    out = []
    out.append("% Canonical CSR footer. Auto-generated by csr_compile.py.")
    out.append(f"% Source: build/footers/{doc.namespace}.tex (regenerated each build)")
    out.append(f"% Last verified: {compiled_at[:10]}")
    out.append("\\vfill")
    out.append("\\noindent\\rule{\\textwidth}{0.4pt}")
    out.append("\\par\\smallskip")
    out.append("\\begin{center}\\footnotesize\\sffamily")
    out.append("\\begin{minipage}{0.92\\textwidth}")
    out.append("\\begin{verbatim}")
    out.append("Corpus Semantic Registry (CSR)")
    out.append(f"Document Version: {doc.namespace} {doc.version}")
    out.append(f"Publication Mode: {doc.publication_mode}")
    out.append(f"Status: {doc.status}")
    out.append(f"Last Verified: {compiled_at[:10]}")
    out.append("")
    if deps:
        out.append("Depends on:")
        for d in deps:
            # Strip the leading "csr." prefix; otherwise keep the full id.
            short = d[4:] if d.startswith("csr.") else d
            out.append(f"- {short}")
    if defines:
        out.append("")
        out.append("Defines (canonical entries):")
        for d in defines:
            short = d[4:] if d.startswith("csr.") else d
            out.append(f"- {short}")
        if len(doc.defines) > 24:
            out.append(f"- ... ({len(doc.defines) - 24} more; see CSR.lock.json)")
    out.append("\\end{verbatim}")
    out.append("\\end{minipage}")
    out.append("\\end{center}")
    return "\n".join(out) + "\n"


def validate_symbol_block_truncation(input_paths) -> List[Diagnostic]:
    """CSR026: scan registry .csr files for symbol blocks that are truncated
    mid-string or carry trailing content past their last_verified close.

    Detects three failure modes observed in production:
    (a) Symbol block ends mid-word (e.g., 'sour' instead of 'source_hash: auto');
        block's last non-blank line doesn't match any valid YAML termination.
    (b) Symbol block has verification: but no last_verified field (truncated
        within verification clause).
    (c) Symbol block has trailing non-blank, non-comment content past its
        last_verified close, before the next top-level declaration.

    Returns a list of Diagnostic objects; empty list if all blocks well-formed.
    The check is structural (regex on parsed line structure), not YAML-dependent;
    it runs before parse so it can give actionable errors even when YAML parse
    would otherwise raise an opaque 'unexpected end of stream'.
    """
    diagnostics: List[Diagnostic] = []
    symbol_start_re = re.compile(r"^symbol\s+(\w+):")
    decl_re = re.compile(
        r"^(symbol|document|alias|invariant|migration|predecessor|promotion_rule|collision)\s"
    )
    last_verified_re = re.compile(r"^\s+last_verified:\s*\d{4}-\d{2}-\d{2}")
    verification_re = re.compile(r"^\s+verification:\s*$")
    valid_termination_re = re.compile(
        r"^\s+[\w-]+:\s*(\S.*)?$"  # field: value
        r"|^\s+-\s+\S+"            # list item
        r"|^\s*\".*\"\s*$"         # closing quoted scalar
    )

    for path in input_paths:
        try:
            text = path.read_text(encoding="utf-8")
        except Exception:
            continue
        lines = text.split("\n")
        # Locate all symbol declarations
        starts: List[Tuple[int, str]] = []
        for i, line in enumerate(lines):
            m = symbol_start_re.match(line)
            if m:
                starts.append((i, m.group(1)))
        if not starts:
            continue
        for idx, (start_line, symname) in enumerate(starts):
            # Determine block end: next top-level declaration or EOF
            end_line = len(lines)
            for j in range(start_line + 1, len(lines)):
                if decl_re.match(lines[j]):
                    end_line = j
                    break
            block = lines[start_line:end_line]
            # Locate verification: and last_verified: within block
            verification_idx = -1
            last_verified_idx = -1
            for j, b in enumerate(block):
                if verification_re.match(b):
                    verification_idx = j
                if last_verified_re.match(b):
                    last_verified_idx = j
            # Last non-blank, non-comment line of block
            last_content_idx = -1
            for j in range(len(block) - 1, -1, -1):
                stripped = block[j].strip()
                if not stripped:
                    continue
                if stripped.startswith("#"):
                    continue
                last_content_idx = j
                break
            if last_content_idx < 0:
                continue
            last_line = block[last_content_idx]
            # Mode (a): last content line of block doesn't look like a valid
            # YAML termination - likely mid-word truncation.
            if not valid_termination_re.match(last_line):
                diagnostics.append(Diagnostic(
                    code="CSR026",
                    message=(
                        f"symbol_block_truncation_check: symbol {symname} in "
                        f"{path.name} ends with malformed line "
                        f"{last_line.strip()!r} (likely truncation)"
                    ),
                    severity="error",
                    file=str(path),
                    line=start_line + last_content_idx + 1,
                ))
                continue
            # Mode (b): verification: present but last_verified missing
            if verification_idx >= 0 and last_verified_idx < 0:
                diagnostics.append(Diagnostic(
                    code="CSR026",
                    message=(
                        f"symbol_block_truncation_check: symbol {symname} in "
                        f"{path.name} has verification: clause but no "
                        f"last_verified field (truncated within verification)"
                    ),
                    severity="error",
                    file=str(path),
                    line=start_line + verification_idx + 1,
                ))
                continue
            # Mode (c): trailing content past last_verified
            if last_verified_idx >= 0:
                # Flag trailing content only at symbol-field indent (<=2) - orphan
                # top-level pollution. Deeper-indented content is legitimate nested
                # structure (e.g., evidence: under verification, source_anchor children).
                for j in range(last_verified_idx + 1, len(block)):
                    line = block[j]
                    stripped = line.strip()
                    if not stripped or stripped.startswith("#"):
                        continue
                    indent = len(line) - len(line.lstrip())
                    if indent > 2:
                        continue
                    diagnostics.append(Diagnostic(
                        code="CSR026",
                        message=(
                            f"symbol_block_truncation_check: trailing content "
                            f"past last_verified in symbol {symname} "
                            f"({path.name}): {stripped[:80]!r}"
                        ),
                        severity="error",
                        file=str(path),
                        line=start_line + j + 1,
                    ))
                    break
    return diagnostics


def compile_registry(input_paths, build_dir, compiled_at=""):
    """Compile one or more .csr files. Returns (errors, warnings).

    If compiled_at is empty, derive a content-stable timestamp from the
    maximum mtime of the inputs (UTC, second precision). This advances on
    real edits while preserving lockfile byte-determinism for unchanged inputs
    (test_lockfile_is_deterministic still passes because both runs see the
    same input mtimes)."""
    if not compiled_at:
        import datetime as _dt
        try:
            max_mtime = max((Path(p).stat().st_mtime for p in input_paths), default=0.0)
            compiled_at = _dt.datetime.utcfromtimestamp(max_mtime).strftime("%Y-%m-%dT%H:%M:%SZ")
        except Exception:
            compiled_at = "1970-01-01T00:00:00Z"
    all_diagnostics = []
    # CSR026: pre-parse structural check for symbol-block truncation.
    # Runs before YAML parse so it can surface actionable errors even when
    # parse would otherwise raise opaque 'unexpected end of stream'.
    truncation_diagnostics = validate_symbol_block_truncation(input_paths)
    all_diagnostics.extend(truncation_diagnostics)
    reg = Registry()
    for path in input_paths:
        text = path.read_text(encoding="utf-8")
        sub_reg, sub_diag = parse(text, file_path=str(path))
        all_diagnostics.extend(sub_diag)
        reg.imports.extend(sub_reg.imports)
        reg.symbols.extend(sub_reg.symbols)
        reg.documents.extend(sub_reg.documents)
        reg.collisions.extend(sub_reg.collisions)
        reg.invariants.extend(sub_reg.invariants)
        reg.promotion_rules.extend(sub_reg.promotion_rules)
        reg.migrations.extend(sub_reg.migrations)
        reg.aliases.extend(sub_reg.aliases)
        reg.predecessors.extend(sub_reg.predecessors)
    validator = Validator(reg)
    validator.build_indexes()
    validator.validate_fields()
    alias_map = validator.resolve_aliases()
    validator.fill_definition_hashes()
    validator.derive_inverses()
    validator.validate_relations(alias_map)
    validator.validate_cycles()
    # CSR021: doc-source resolvability (warns when no readable source file exists on disk)
    try:
        # Match csr_extract.PF_ROOT_FROM_CSR for this deployment.
        # The registry dir sits one level below corpus_root; build_dir is
        # <registry>/build/. So corpus_root = build_dir.parent.parent (two up).
        _corpus_root_for_check = build_dir.resolve().parent.parent if hasattr(build_dir, "resolve") else None
    except Exception:
        _corpus_root_for_check = None
    validator.validate_doc_sources(_corpus_root_for_check)
    validator.validate_source_hash_drift(_corpus_root_for_check)
    all_diagnostics.extend(validator.diagnostics)

    build_dir.mkdir(parents=True, exist_ok=True)
    # Derive corpus_root for HTML link existence-checks: build_dir is .../csr/build/,
    # build_dir is <corpus_root>/<subdir>/csr/build by default; corpus_root
    # is build_dir.parent.parent.parent. Adjust if layout differs.
    try:
        corpus_root = build_dir.resolve().parent.parent.parent
    except Exception:
        corpus_root = None
    lockfile = emit_lockfile(reg, compiled_at=compiled_at)
    lockfile["diagnostics"] = [
        {"code": d.code, "severity": d.severity, "message": d.message,
         "file": d.file, "line": d.line}
        for d in all_diagnostics
    ]
    (build_dir / "CSR.lock.json").write_text(
        json.dumps(lockfile, indent=2, sort_keys=True),
        encoding="utf-8",
    )

    errors = sum(1 for d in all_diagnostics if d.severity == "error")
    warnings = sum(1 for d in all_diagnostics if d.severity == "warn")
    infos = sum(1 for d in all_diagnostics if d.severity == "info")
    lines = [
        "CSR v0.1.1 validation report",
        f"Compiled at: {compiled_at}",
        f"Inputs: {[str(p) for p in input_paths]}",
        f"Symbols: {len(reg.symbols)}, Documents: {len(reg.documents)}, "
        f"Collisions: {len(reg.collisions)}, Aliases: {len(reg.aliases)}",
        f"Errors: {errors}, Warnings: {warnings}, Infos: {infos}",
        "",
    ]
    for d in all_diagnostics:
        lines.append(d.format())
    lines.append("")
    (build_dir / "CSR.validation.txt").write_text("\n".join(lines), encoding="utf-8")

    # Phase 1D rendered outputs
    (build_dir / "CSR.overview.md").write_text(
        render_overview_md(reg, compiled_at, errors, warnings), encoding="utf-8"
    )
    (build_dir / "CSR.symbols.md").write_text(
        render_symbols_md(reg, compiled_at), encoding="utf-8"
    )
    (build_dir / "CSR.documents.md").write_text(
        render_documents_md(reg, compiled_at), encoding="utf-8"
    )
    (build_dir / "CSR.collisions.md").write_text(
        render_collisions_md(reg, compiled_at), encoding="utf-8"
    )
    (build_dir / "CSR.status.md").write_text(
        render_status_md(reg, compiled_at), encoding="utf-8"
    )
    (build_dir / "CSR.dependencies.dot").write_text(
        render_dependencies_dot(reg, compiled_at), encoding="utf-8"
    )
    (build_dir / "CSR.wiki.md").write_text(
        render_wiki_md(reg, compiled_at, errors, warnings), encoding="utf-8"
    )
    # HTML rendering: self-contained styled view with embedded SVG dependency graph.
    svg_path = build_dir / "CSR.dependencies.svg"
    svg_inline = svg_path.read_text(encoding="utf-8") if svg_path.exists() else ""

    # Registry browser (fast, deterministic) renders first so it always
    # ships even when the heavier snapshot stalls on pandoc invocations.
    (build_dir / "CSR.registry.html").write_text(
        render_registry_html(reg, compiled_at, errors, warnings, corpus_root=corpus_root),
        encoding="utf-8",
    )

    # Snapshot is opt-in: set CSR_BUILD_SNAPSHOT=1 to render. With several
    # hundred wiki-anchored symbols, the snapshot's per-symbol pandoc costs
    # dominate the build. The registry view stays the canonical browser.
    if os.environ.get("CSR_BUILD_SNAPSHOT") == "1":
        (build_dir / "CSR.snapshot.html").write_text(
            render_wiki_html(reg, compiled_at, errors, warnings, svg_inline),
            encoding="utf-8",
        )
    # Also keep CSR.wiki.html as a mirror of the registry browser, so older
    # bookmarks targeting CSR.wiki.html still resolve to a current view.
    (build_dir / "CSR.wiki.html").write_text(
        render_registry_html(reg, compiled_at, errors, warnings, corpus_root=corpus_root),
        encoding="utf-8",
    )

    footers_dir = build_dir / "footers"
    footers_dir.mkdir(parents=True, exist_ok=True)
    for doc in reg.documents:
        (footers_dir / f"{doc.namespace}.tex").write_text(
            render_doc_footer(doc, reg, compiled_at),
            encoding="utf-8",
        )

    (build_dir / "consolidated_doc_registry.tex").write_text(
        render_consolidated_doc_registry(reg, compiled_at),
        encoding="utf-8",
    )
    (build_dir / "consolidated_symbol_registry.tex").write_text(
        render_consolidated_symbol_registry(reg, compiled_at),
        encoding="utf-8",
    )

    return errors, warnings


# ----------------------------------------------------------------------------
# Tail-integrity guard. If Edit-tool truncation drops bytes past this point,
# the assertion below fires on import and the build fails loudly instead of
# silently rendering stale HTML. The check looks for a string constant from
# the last write inside compile_registry; truncation that removes that final
# write also removes the constant from the function's bytecode.
# ------------------------------------------------------------------
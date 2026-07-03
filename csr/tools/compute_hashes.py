"""compute_hashes.py - drift-detection pass.

Walks the CSR registry, finds the source file for each document, computes
SHA256 of the file content, and patches every symbol's source_anchor with
real source_hash and section_hash values. At v0 the section_hash equals
the document hash (we don't yet extract per-section content from TeX).
This is conservative: the document-level hash detects "any source change"
which is the load-bearing drift signal.

Run from the corpus root or pass --root.

Output:
- patches every registry/*.csr file in place, replacing absent
  source_hash and section_hash with computed values
- prints a coverage report (docs found vs missing)
- the resulting CSR build emits CSR020 only for symbols whose owning
  document's source file was not found - those are the real gaps
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


# HINTS table retired 2026-05-08: all docs declare inline source_path: in documents.csr.
HINTS = {}

# FRAMEWORK_MD table retired 2026-05-08: all framework notes declare inline source_path:.
FRAMEWORK_MD = {}


def candidate_paths(did: str, doc: dict) -> list[str]:
    ns = doc.get("namespace", "")
    ver = doc.get("version", "v0")
    ver_no_v = ver.lstrip("v")
    parts = ver_no_v.split(".")
    ver_major = "v" + parts[0]
    ver_minor = "v" + ".".join(parts[:2]) if len(parts) >= 2 else ver_major
    ver_dotless = ver.replace(".", "")
    ver_dot_to_us = ver_no_v.replace(".", "_")

    out: list[str] = []
    seen: set[str] = set()
    def add(s: str) -> None:
        if s and s not in seen:
            seen.add(s)
            out.append(s)

    # Try full version, then minor, then major as fallback for any HINT pattern
    for fmt in HINTS.get(ns, []):
        for v in (ver, ver_minor, ver_major):
            try:
                add(fmt.format(
                    ver=v,
                    ver_no_v=v.lstrip("v"),
                    ver_dotless=v.replace(".", ""),
                    ver_dot_to_us=v.lstrip("v").replace(".", "_"),
                    ver_major=ver_major,
                    ver_minor=ver_minor,
                ))
            except (KeyError, IndexError):
                pass
    if did in FRAMEWORK_MD:
        for s in FRAMEWORK_MD[did]:
            add(s)
    add(f"{ns}_{ver}.tex")
    add(f"{ns}_{ver_major}.tex")
    add(f"{ns}.tex")
    add(f"{ns}.md")
    return out


def find_source(did: str, doc: dict, root: Path) -> Path | None:
    # Preferred path: the document declares source_path explicitly in its CSR block.
    explicit = doc.get("source_path")
    if explicit:
        p = root / explicit
        if p.exists():
            return p
        # explicit path declared but missing: do not fall through to HINTS, surface the gap
        return None
    # Legacy prefix_map. In the seed template this is empty; every document
    # should declare an explicit source_path. Populate this map per-project if
    # you want legacy short-prefix fallbacks (e.g. "preprints/foo" -> "<dir>/foo").
    prefix_map = {
        "ukraine/":           ukraine,
        "logistics/":         logistics,
        "root/":              root,
    }
    for cand in candidate_paths(did, doc):
        matched_prefix = False
        for prefix, base in prefix_map.items():
            if cand.startswith(prefix):
                p = base / cand[len(prefix):]
                if p.exists():
                    return p
                matched_prefix = True
                break
        if matched_prefix:
            continue
        for base in [thesis, thesis / "csr"]:
            p = base / cand
            if p.exists():
                return p
    return None


def sha256_of(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return f"sha256:{h.hexdigest()}"


def patch_csr_file(csr_file: Path, doc_id_to_hash: dict[str, str], symbol_owner: dict[str, str], force: bool = False) -> int:
    """Insert source_hash and section_hash lines into source_anchor blocks
    that don't already have them. Returns the number of edits applied."""
    text = csr_file.read_text(encoding="utf-8")

    # Find each symbol block and its source_anchor sub-block.
    # Rather than parse YAML, do line-level patching: for each
    # 'source_anchor:' line, find the matching 'anchor:' line below it
    # (the canonical last field of the source_anchor block per the schema),
    # then insert source_hash and section_hash lines after the anchor line
    # if they're not already present.

    pattern = re.compile(r"^symbol\s+([\w_]+):\s*$", re.MULTILINE)
    edits = 0
    new_lines = []
    lines = text.split("\n")
    i = 0
    current_sym_id = None

    while i < len(lines):
        line = lines[i]
        m = re.match(r"^\s*id:\s*(csr\.[\w_.]+)\s*$", line)
        if m and "csr.document." not in m.group(1):
            current_sym_id = m.group(1)
        # Look for source_anchor block
        if line.strip() == "source_anchor:":
            # Indent of children is the indent of source_anchor + 2 spaces
            indent = len(line) - len(line.lstrip())
            child_indent = " " * (indent + 2)
            # Scan ahead for the source_anchor block's lines
            block_start = i
            j = i + 1
            block_lines = []
            has_source_hash = False
            has_section_hash = False
            anchor_line_idx = None
            while j < len(lines):
                child = lines[j]
                if child.strip() == "":
                    break
                if not child.startswith(child_indent):
                    break
                block_lines.append((j, child))
                stripped = child.strip()
                if stripped.startswith("source_hash:"):
                    has_source_hash = True
                if stripped.startswith("section_hash:"):
                    has_section_hash = True
                if stripped.startswith("anchor:"):
                    anchor_line_idx = j
                j += 1
            # Determine the doc this symbol belongs to.
            owner = symbol_owner.get(current_sym_id or "", "")
            doc_hash = doc_id_to_hash.get(owner)
            needs_patch = doc_hash is not None and anchor_line_idx is not None and (
                force or not (has_source_hash and has_section_hash)
            )
            if needs_patch:
                # In force mode, drop any existing source_hash/section_hash lines
                # from the source_anchor block first (we'll rewrite them).
                if force:
                    block_lines = [(j, ln) for (j, ln) in block_lines
                                   if not ln.strip().startswith(("source_hash:", "section_hash:"))]
                # Insert source_hash and section_hash right after anchor line.
                insert_pos = anchor_line_idx + 1
                # If force removed stale lines, the upper bound j may include them; rebuild
                # by writing the (possibly filtered) block_lines, then the fresh hash lines.
                if force:
                    new_lines.append(lines[i])  # the source_anchor: line itself
                    for (jj, ln) in block_lines:
                        if jj <= anchor_line_idx:
                            new_lines.append(ln)
                    new_lines.append(f"{child_indent}source_hash: {doc_hash}")
                    new_lines.append(f"{child_indent}section_hash: {doc_hash}")
                    for (jj, ln) in block_lines:
                        if jj > anchor_line_idx:
                            new_lines.append(ln)
                    edits += 2
                    # advance i past the original source_anchor block end
                    i = j  # j is the end-of-block index from the scan above
                    continue
                else:
                    new_lines.extend(lines[i:insert_pos])
                    if not has_source_hash:
                        new_lines.append(f"{child_indent}source_hash: {doc_hash}")
                        edits += 1
                    if not has_section_hash:
                        new_lines.append(f"{child_indent}section_hash: {doc_hash}")
                        edits += 1
                    i = insert_pos
                    continue
        new_lines.append(line)
        i += 1

    if edits:
        csr_file.write_text("\n".join(new_lines), encoding="utf-8")
    return edits


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Compute and patch CSR source/section hashes.")
    parser.add_argument("--root", default=".", help="corpus root directory (containing csr/ subtree somewhere)")
    parser.add_argument("--lock", default="csr/build/CSR.lock.json")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--force", action="store_true",
                        help="rewrite existing source_hash/section_hash lines (use after switching source_path)")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    lock_path = root / args.lock
    lock = json.loads(lock_path.read_text(encoding="utf-8"))
    docs = lock["documents"]
    syms = lock["symbols"]

    # Discovery
    found = {}
    missing = []
    for did, doc in docs.items():
        p = find_source(did, doc, root)
        if p:
            found[did] = p
        else:
            missing.append(did)

    print(f"docs found:   {len(found)}/{len(docs)}")
    print(f"docs missing: {len(missing)}")
    if missing:
        print("missing source files (CSR020 will keep firing on these):")
        for did in sorted(missing):
            ns = docs[did].get("namespace", "")
            ver = docs[did].get("version", "")
            print(f"  - {did}  ns={ns} ver={ver}")

    # Compute hashes once per source file
    doc_hashes = {did: sha256_of(p) for did, p in found.items()}
    symbol_owner = {sid: s.get("owning_document", "") for sid, s in syms.items()}

    if args.dry_run:
        print(f"\n--dry-run: would patch hashes for symbols owned by {len(found)} docs")
        return 0

    # Patch each .csr file
    # In the seed template, csr/ is expected directly under root.
    # Adjust if your layout nests csr/ deeper.
    registry_dir = root / "csr" / "registry"
    total_edits = 0
    for csr_file in sorted(registry_dir.glob("*.csr")):
        if csr_file.name in {"CSR.csr", "documents.csr", "aliases.csr",
                             "collisions_resolved.csr", "invariants.csr",
                             "migration.csr", "predecessors.csr"}:
            continue
        edits = patch_csr_file(csr_file, doc_hashes, symbol_owner, force=args.force)
        if edits:
            print(f"  {csr_file.name}: +{edits} hash lines")
            total_edits += edits

    print(f"\ntotal hash lines added: {total_edits}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

"""
corpus_dump.py — concatenate every registered document into a single .md.

Walks all csr/registry/*.csr files, finds each `document` block, reads the
source file from `source_path`, and emits a single Markdown artifact where
each document is a chapter with YAML frontmatter carrying its CSR metadata.

Output: build/Corpus_Dump.md (default) — self-describing, greppable,
LLM-ingestible. Raw LaTeX math passes through as-is.

Usage:
    python3 corpus_dump.py [--output PATH] [--class CLASS [CLASS ...]] [--root ROOT]

Filters:
    --class framework framework_preprint    only those classes
    --status canonical candidate            only those statuses

The PF root is auto-detected by walking up from this file location:
    csr/tools/corpus_dump.py -> csr/ -> <corpus_root>/
"""

from __future__ import annotations

import argparse
import re
import sys
import time
import os
from pathlib import Path

DEFAULT_OUTPUT = "build/Corpus_Dump.md"


def find_corpus_root(start: Path) -> Path:
    """Walk up from start until we find a directory containing a `csr/` subdirectory.

    Marker: presence of `csr/registry/documents.csr` (sufficient to identify a
    CSR-managed corpus root). Override the marker file via the CSR_ROOT_MARKER
    env var if needed.
    """
    marker = os.environ.get("CSR_ROOT_MARKER", "csr/registry/documents.csr")
    p = start.resolve()
    for _ in range(8):
        if (p / marker).is_file():
            return p
        if p.parent == p:
            break
        p = p.parent
    raise FileNotFoundError(f"Could not find corpus root walking up from {start}; marker {marker} not found")


DOC_HEADER_RE = re.compile(r"(?m)^document\s+(\S+):")
FIELD_RE = re.compile(r"(?m)^\s+([a-z_]+):\s*(.*)$")
LIST_ITEM_RE = re.compile(r"(?m)^\s+-\s+(\S+)\s*$")


def parse_document_blocks(text: str):
    """Yield (name, block_body_text) for each document block in a .csr file."""
    matches = list(DOC_HEADER_RE.finditer(text))
    for i, m in enumerate(matches):
        name = m.group(1).rstrip(":")
        body_start = m.end()
        body_end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        yield name, text[body_start:body_end]


def parse_doc_fields(block: str) -> dict:
    """Extract top-level fields from a document block body."""
    out: dict = {}
    # Single-value fields
    for line in block.splitlines():
        mm = re.match(r"^  ([a-z_]+):\s*(.*)$", line)
        if mm:
            key = mm.group(1)
            val = mm.group(2).strip()
            if val and not val.endswith(":"):
                out[key] = val.strip('"')
    # Lists (defines, depends_on)
    for list_key in ("defines", "depends_on"):
        items = []
        # Find the list_key line and collect indented bullets that follow
        kv = re.search(rf"(?m)^  {list_key}:\s*\n((?:    -\s+\S.*\n)+)", block)
        if kv:
            for it in re.finditer(r"-\s+(\S+)", kv.group(1)):
                items.append(it.group(1))
        if items:
            out[list_key] = items
    return out


def yaml_frontmatter(name: str, fields: dict) -> str:
    """Emit a YAML frontmatter block for a document."""
    lines = ["---", f"doc_id: csr.document.{name}"]
    order = [
        "namespace", "display_name", "version", "status", "document_class",
        "publication_mode", "predecessor_version", "source_path", "last_verified",
    ]
    for k in order:
        if k in fields:
            v = fields[k]
            if " " in v or ":" in v:
                v = f'"{v}"'
            lines.append(f"{k}: {v}")
    if "defines" in fields and fields["defines"]:
        lines.append("defines:")
        for s in fields["defines"]:
            lines.append(f"  - {s}")
    if "depends_on" in fields and fields["depends_on"]:
        lines.append("depends_on:")
        for s in fields["depends_on"]:
            lines.append(f"  - {s}")
    lines.append("---")
    return "\n".join(lines)


def read_source(pf_root: Path, source_path: str) -> tuple[str, str | None]:
    """Read source file content. Returns (content, error_or_None)."""
    p = pf_root / source_path
    if not p.exists():
        return "", f"source file not found: {source_path}"
    if p.suffix == ".docx":
        # Skip binary; just note its presence
        return f"[binary .docx file at {source_path} — not inlined in dump]", None
    try:
        with open(p, "r", encoding="utf-8", errors="replace") as f:
            return f.read(), None
    except Exception as e:
        return "", f"read error: {e}"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default=DEFAULT_OUTPUT,
                        help=f"output path relative to csr/ (default: {DEFAULT_OUTPUT})")
    parser.add_argument("--class", dest="filter_class", nargs="*", default=None,
                        help="filter to these document_class values (default: all)")
    parser.add_argument("--status", dest="filter_status", nargs="*", default=None,
                        help="filter to these status values (default: all)")
    parser.add_argument("--root", default=None,
                        help="path to csr/ directory (default: auto-detect)")
    args = parser.parse_args()

    here = Path(__file__).parent
    csr_root = Path(args.root).resolve() if args.root else here.parent
    pf_root = find_corpus_root(csr_root)

    registry_dir = csr_root / "registry"
    if not registry_dir.is_dir():
        print(f"ERROR: registry directory not found at {registry_dir}", file=sys.stderr)
        return 1

    # Gather all document blocks
    docs = []
    for csr_file in sorted(registry_dir.glob("*.csr")):
        text = csr_file.read_text(encoding="utf-8", errors="replace")
        for name, block in parse_document_blocks(text):
            fields = parse_doc_fields(block)
            fields["_registry_file"] = csr_file.name
            fields["_name"] = name
            docs.append((name, fields))

    # Apply filters
    if args.filter_class:
        docs = [d for d in docs if d[1].get("document_class") in args.filter_class]
    if args.filter_status:
        docs = [d for d in docs if d[1].get("status") in args.filter_status]

    # Sort: by document_class, then by namespace, then by name
    class_order = {
        "framework": 0,
        "framework_preprint": 1,
        "domain_application": 2,
        "field_note": 3,
        "product": 4,
        "pitch": 5,
        "outreach": 6,
        "business": 7,
        "index": 8,
        "personal": 9,
    }
    docs.sort(key=lambda d: (
        class_order.get(d[1].get("document_class", ""), 99),
        d[1].get("namespace", ""),
        d[0],
    ))

    # Emit
    output_path = csr_root / args.output
    output_path.parent.mkdir(parents=True, exist_ok=True)

    written = 0
    missing_source = 0
    total_bytes = 0
    parts = []

    parts.append("# Corpus Dump")
    parts.append("")
    parts.append(f"Generated: {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}")
    parts.append(f"Source: {csr_root}")
    parts.append(f"Documents: {len(docs)}")
    if args.filter_class:
        parts.append(f"Filter (class): {', '.join(args.filter_class)}")
    if args.filter_status:
        parts.append(f"Filter (status): {', '.join(args.filter_status)}")
    parts.append("")
    parts.append("Each document below begins with a YAML frontmatter block carrying its CSR metadata, followed by the raw source content of the document. LaTeX math passes through as raw markup. Binary files (.docx) are noted but not inlined.")
    parts.append("")
    parts.append("---")
    parts.append("")
    # Table of contents
    parts.append("## Table of contents")
    parts.append("")
    current_class = None
    for name, f in docs:
        cls = f.get("document_class", "(unclassified)")
        if cls != current_class:
            parts.append(f"\n### {cls}\n")
            current_class = cls
        ns = f.get("namespace", "")
        ver = f.get("version", "")
        parts.append(f"- `csr.document.{name}` ({ns}, {ver})")
    parts.append("")
    parts.append("---")
    parts.append("")

    # Documents
    for name, fields in docs:
        src = fields.get("source_path")
        if not src:
            missing_source += 1
            continue
        content, err = read_source(pf_root, src)
        if err:
            missing_source += 1
            parts.append(f"\n\n# {name}\n\n{yaml_frontmatter(name, fields)}\n\n*[{err}]*\n")
            continue
        total_bytes += len(content)
        written += 1
        # Doc header
        parts.append(f"\n\n# {name}")
        parts.append("")
        parts.append(yaml_frontmatter(name, fields))
        parts.append("")
        # Fence-protect .tex content from markdown chrome
        if src.endswith(".tex"):
            parts.append("```latex")
            parts.append(content.rstrip())
            parts.append("```")
        elif src.endswith(".lean"):
            parts.append("```lean")
            parts.append(content.rstrip())
            parts.append("```")
        else:
            # md, txt, etc — let through as-is
            parts.append(content.rstrip())

    output_path.write_text("\n".join(parts) + "\n", encoding="utf-8")

    print(f"Documents in registry: {len(docs)}")
    print(f"Written with content : {written}")
    print(f"Missing source files : {missing_source}")
    print(f"Total content bytes  : {total_bytes:,}")
    print(f"Output               : {output_path}")
    print(f"Output size          : {output_path.stat().st_size:,} bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())

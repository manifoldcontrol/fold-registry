"""
csr - Corpus Semantic Registry CLI dispatcher.

Subcommands:
  build        Compile registry and emit lockfile + rendered views.
  watch        Auto-rebuild on .csr file changes (polls every 1s).
  view         Open rendered CSR.wiki.md in default browser/viewer.
  info         Print registry summary to terminal.
  serve        Run a local HTTP server for the rendered views (opt-in).
  pack         Build a self-contained .pyz zipapp distribution.

Run from the csr/ root directory or pass --root to point at it.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Optional

# Ensure csr_compile is importable from the same directory
_HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(_HERE))

import csr_compile  # type: ignore

# Tail-integrity guard: the Edit tool has been observed to silently truncate
# csr_compile.py mid-write, leaving compile_registry without its tail. The
# function then returns None instead of (errors, warnings) and the build
# rendered stale HTML for half an hour before the symptom surfaced. The
# check below verifies a string constant from the LAST write inside
# compile_registry is present in the function's bytecode. Truncation that
# drops that final write also drops the constant. Cheap, structural, fires
# on import.
assert callable(getattr(csr_compile, "compile_registry", None)) and \
    "consolidated_symbol_registry.tex" in csr_compile.compile_registry.__code__.co_consts, \
    "csr_compile.py appears truncated; compile_registry is missing its tail"


def find_registry_root(explicit: Optional[str]) -> Path:
    """Locate the csr/ root directory."""
    if explicit:
        root = Path(explicit).resolve()
    else:
        # Walk up from cwd looking for a registry/ subdirectory
        cwd = Path.cwd().resolve()
        for candidate in [cwd] + list(cwd.parents):
            if (candidate / "registry").is_dir() and (candidate / "tools").is_dir():
                root = candidate
                break
        else:
            # Fall back to the directory containing this script's parent
            root = _HERE.parent
    if not (root / "registry").is_dir():
        sys.exit(f"error: no registry/ directory under {root}")
    return root


def gather_inputs(root: Path) -> List[Path]:
    """Auto-glob registry/*.csr (excluding the root CSR.csr index)."""
    inputs = sorted(
        p for p in (root / "registry").glob("*.csr")
        if p.name != "CSR.csr"  # skip the import-only root
    )
    if not inputs:
        sys.exit(f"error: no .csr files found under {root / 'registry'}")
    return inputs


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def cmd_build(args: argparse.Namespace) -> int:
    root = find_registry_root(args.root)
    inputs = gather_inputs(root)
    build_dir = root / args.build_dir
    errors, warnings = csr_compile.compile_registry(
        inputs, build_dir, compiled_at=args.compiled_at,
    )
    print(f"[csr build] inputs={len(inputs)} errors={errors} warnings={warnings}")
    if errors == 0 and warnings == 0:
        print(f"[csr build] outputs in {build_dir}")
    return 0 if errors == 0 else 1


# ----------------------------------------------------------------------------
# watch
# ----------------------------------------------------------------------------

def _snapshot_mtimes(paths: List[Path]) -> dict:
    return {p: p.stat().st_mtime for p in paths if p.exists()}


def cmd_watch(args: argparse.Namespace) -> int:
    root = find_registry_root(args.root)
    inputs = gather_inputs(root)
    build_dir = root / args.build_dir

    print(f"[csr watch] watching {len(inputs)} files under {root / 'registry'}")
    print(f"[csr watch] press Ctrl-C to stop")

    last_state = {}
    try:
        while True:
            current_inputs = gather_inputs(root)  # re-glob in case files were added
            current = _snapshot_mtimes(current_inputs)
            if current != last_state:
                added = set(current) - set(last_state)
                removed = set(last_state) - set(current)
                changed = {p for p in current if p in last_state and current[p] != last_state[p]}
                if last_state:  # not the initial snapshot
                    summary = []
                    if added:    summary.append(f"+{len(added)}")
                    if removed:  summary.append(f"-{len(removed)}")
                    if changed:  summary.append(f"~{len(changed)}")
                    print(f"\n[csr watch] change detected ({', '.join(summary)})")
                errors, warnings = csr_compile.compile_registry(
                    current_inputs, build_dir, compiled_at=args.compiled_at,
                )
                stamp = time.strftime("%H:%M:%S")
                status = "OK" if errors == 0 else "FAIL"
                print(f"[csr watch {stamp}] {status} errors={errors} warnings={warnings}")
                last_state = current
            time.sleep(args.interval)
    except KeyboardInterrupt:
        print("\n[csr watch] stopped")
        return 0


# ----------------------------------------------------------------------------
# view
# ----------------------------------------------------------------------------

def cmd_view(args: argparse.Namespace) -> int:
    root = find_registry_root(args.root)
    target = root / args.build_dir / args.file

    if not target.exists():
        print(f"[csr view] {target} not found, running build first")
        cmd_build(args)
        if not target.exists():
            sys.exit(f"[csr view] {target} still missing after build")

    # Open with the OS default handler
    if sys.platform == "win32":
        os.startfile(str(target))  # type: ignore
    elif sys.platform == "darwin":
        subprocess.run(["open", str(target)])
    else:
        # Linux / WSL: try xdg-open, fall back to printing path
        try:
            subprocess.run(["xdg-open", str(target)], check=False)
        except FileNotFoundError:
            print(f"[csr view] {target}")
    return 0


# ----------------------------------------------------------------------------
# info
# ----------------------------------------------------------------------------

def cmd_info(args: argparse.Namespace) -> int:
    root = find_registry_root(args.root)
    lockfile_path = root / args.build_dir / "CSR.lock.json"
    if not lockfile_path.exists():
        print(f"[csr info] no lockfile yet, running build")
        cmd_build(args)

    with open(lockfile_path, encoding="utf-8") as f:
        lock = json.load(f)

    print(f"CSR {lock['registry']} v{lock['version']}")
    print(f"Compiled at: {lock['compiled_at']}")
    print()
    counts = [
        ("Symbols",     len(lock.get("symbols", {}))),
        ("Documents",   len(lock.get("documents", {}))),
        ("Collisions",  len(lock.get("collisions", {}))),
        ("Aliases",     len(lock.get("aliases", {}))),
        ("Invariants",  len(lock.get("invariants", {}))),
        ("Migrations",  len(lock.get("migrations", {}))),
        ("Diagnostics", len(lock.get("diagnostics", []))),
    ]
    for label, n in counts:
        print(f"  {label:14} {n}")
    print()

    # By status
    status_counts: dict = {}
    for s in lock.get("symbols", {}).values():
        status_counts[s["status"]] = status_counts.get(s["status"], 0) + 1
    if status_counts:
        print("Symbols by status:")
        for st, n in sorted(status_counts.items()):
            print(f"  {st:14} {n}")
        print()

    # Open diagnostics
    diags = lock.get("diagnostics", [])
    if diags:
        errors = [d for d in diags if d.get("severity") == "error"]
        warnings = [d for d in diags if d.get("severity") == "warn"]
        print(f"Diagnostics: {len(errors)} error(s), {len(warnings)} warning(s)")
    else:
        print("Diagnostics: clean")
    return 0


# ----------------------------------------------------------------------------
# serve (optional small HTTP server for the build/ dir)
# ----------------------------------------------------------------------------

def cmd_serve(args: argparse.Namespace) -> int:
    import http.server
    import socketserver

    root = find_registry_root(args.root)
    serve_dir = root / args.build_dir
    if not serve_dir.exists():
        print(f"[csr serve] no build/ yet, running build")
        cmd_build(args)

    os.chdir(serve_dir)
    handler = http.server.SimpleHTTPRequestHandler

    with socketserver.TCPServer(("", args.port), handler) as httpd:
        url = f"http://localhost:{args.port}/CSR.wiki.md"
        print(f"[csr serve] http://localhost:{args.port}/  (Ctrl-C to stop)")
        print(f"[csr serve] wiki: {url}")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\n[csr serve] stopped")
    return 0


# ----------------------------------------------------------------------------
# pack (zipapp)
# ----------------------------------------------------------------------------

def cmd_pack(args: argparse.Namespace) -> int:
    """Build a single-file .pyz zipapp distribution."""
    import shutil
    import tempfile
    import zipapp

    root = find_registry_root(args.root)
    out_path = root / args.output

    with tempfile.TemporaryDirectory() as tmpdir:
        src = Path(tmpdir) / "src"
        src.mkdir()
        # Copy the two Python sources into the bundle
        shutil.copy(_HERE / "csr_compile.py", src / "csr_compile.py")
        shutil.copy(_HERE / "csr.py", src / "__main__.py")
        # Record version + manifest
        (src / "VERSION").write_text("CSR v0.1.1 zipapp\n")

        zipapp.create_archive(
            source=src,
            target=out_path,
            interpreter="/usr/bin/env python3",
            compressed=True,
        )

    print(f"[csr pack] wrote {out_path} ({out_path.stat().st_size} bytes)")
    print(f"[csr pack] run with: python3 {out_path} <subcommand>")
    return 0


# ----------------------------------------------------------------------------
# refresh
# ----------------------------------------------------------------------------

def cmd_refresh(args: argparse.Namespace) -> int:
    """Idempotent bootstrap: build (so lockfile knows new docs), compute_hashes
    (patches missing source/section hashes), build (verifies clean).

    Closes the cwd footgun: compute_hashes must run from corpus root,
    csr build must run from csr/. This handler invokes both correctly
    regardless of the user's cwd."""
    import subprocess
    root = find_registry_root(args.root)
    corpus_root = root.parent.parent  # csr/ -> <subdir>/ -> <corpus_root>/

    # Pre-build: ensures lockfile has any new doc declarations.
    inputs = gather_inputs(root)
    build_dir = root / args.build_dir
    errors, warnings = csr_compile.compile_registry(
        inputs, build_dir, compiled_at=args.compiled_at,
    )
    if errors:
        print(f"[csr refresh] pre-build failed: errors={errors}")
        return 1
    print(f"[csr refresh] pre-build OK  (errors=0 warnings={warnings})")

    # compute_hashes from corpus root
    ch = Path(__file__).resolve().parent / "compute_hashes.py"
    r = subprocess.run([sys.executable, str(ch)], cwd=str(corpus_root),
                       capture_output=True, text=True)
    if r.returncode != 0:
        print("[csr refresh] compute_hashes failed:")
        print(r.stdout[-1500:])
        print(r.stderr[-1500:])
        return 1
    # surface the patched line count
    last_line = next((ln for ln in reversed(r.stdout.splitlines()) if ln.strip()), "")
    print(f"[csr refresh] {last_line.strip()}")

    # Final build: verifies the patched registry is clean
    errors, warnings = csr_compile.compile_registry(
        inputs, build_dir, compiled_at=args.compiled_at,
    )
    print(f"[csr refresh] final build  errors={errors} warnings={warnings}")
    return 0 if errors == 0 else 1


def cmd_lookup(args: argparse.Namespace) -> int:
    """Concept-by-content search across the registry.

    Matches the phrase against symbol id, display_name, definition, aliases,
    predecessors. Returns top N matches with id, owning_document, status,
    predecessors, superseded_by, supersedes."""
    root = find_registry_root(args.root)
    lock_path = root / args.build_dir / "CSR.lock.json"
    if not lock_path.exists():
        print(f"[csr lookup] no lockfile at {lock_path}; run csr build first")
        return 1
    lock = json.loads(lock_path.read_text(encoding="utf-8"))
    syms = lock.get("symbols", {})
    docs = lock.get("documents", {})

    needle = args.phrase.lower()

    matches = []
    for sid, s in syms.items():
        score = 0
        if needle in sid.lower():
            score += 50
        dn = (s.get("display_name") or "").lower()
        if needle in dn:
            score += 30
        defn = (s.get("definition") or "").lower()
        if needle in defn:
            score += 10
            pos = defn.find(needle)
            if pos < 80:
                score += 5
        if score > 0:
            matches.append((score, sid, s))

    matches.sort(key=lambda t: -t[0])
    matches = matches[:args.limit]

    retired_aliases = {
        "spectral fidelity": ("csr.CI.ALG_I_tuple", "Algebraic Integrity (4-factor: perturb/verify/reuse/retain) + Lift/Drift dynamics + 3 control modes (Soliton/Architect/Bootstrap). Memory: feedback_integrity_not_sf.md"),
        "sf": ("csr.CI.ALG_I_tuple", "Algebraic Integrity (4-factor + Lift/Drift + 3 control modes)"),
    }
    if needle in retired_aliases:
        canonical_id, canonical_descr = retired_aliases[needle]
        print(f"WARNING: {args.phrase!r} is RETIRED vocabulary.")
        print(f"  Canonical successor: {canonical_id}")
        print(f"  Apparatus:           {canonical_descr}")
        print()

    if not matches:
        print(f"[csr lookup] no matches for {args.phrase!r}")
        return 0

    print(f"[csr lookup] {args.phrase!r} -- {len(matches)} match(es)\n")
    for score, sid, s in matches:
        owner = s.get("owning_document", "")
        owner_doc = docs.get(owner, {})
        owner_status = owner_doc.get("status", "?")
        owner_version = owner_doc.get("version", "?")
        sup = s.get("supersedes") or []
        sup_by = s.get("superseded_by") or []
        defn = s.get("definition") or ""
        defn_short = defn[:120].replace("\n", " ").strip()
        if len(defn) > 120:
            defn_short += "..."
        print(f"  [{score:3d}]  {sid}")
        print(f"          status={s.get('status','?')}  type={s.get('type','?')}  ns={s.get('namespace','?')}")
        if owner:
            print(f"          owning_document={owner}  ({owner_status} {owner_version})")
        if sup:
            print(f"          supersedes:    {', '.join(sup)}")
        if sup_by:
            print(f"          superseded_by: {', '.join(sup_by)}")
        if defn_short:
            print(f"          \"{defn_short}\"")
        print()

    return 0


def cmd_deps(args: argparse.Namespace) -> int:
    """Transitive dependency / used-by closure with depth budget."""
    root = find_registry_root(args.root)
    lock_path = root / args.build_dir / "CSR.lock.json"
    if not lock_path.exists():
        print(f"[csr deps] no lockfile at {lock_path}; run csr build first")
        return 1
    lock = json.loads(lock_path.read_text(encoding="utf-8"))
    syms = lock.get("symbols", {})

    target = args.symbol_id
    if target not in syms:
        candidates = [k for k in syms if k.endswith(target) or k.endswith("." + target)]
        if len(candidates) == 1:
            target = candidates[0]
            print(f"[csr deps] resolved {args.symbol_id!r} -> {target}")
        elif len(candidates) > 1:
            print(f"[csr deps] ambiguous; candidates:")
            for c in candidates[:10]:
                print(f"  {c}")
            return 1
        else:
            print(f"[csr deps] no such symbol: {args.symbol_id}")
            return 1

    edge_field = "used_by" if args.inverse else "depends_on"
    # composes_with is symmetric (per CSR spec §B.10) - always traversed in
    # both forward and inverse modes. Edges appear in both directions in
    # lock.json after the auto-symmetrise pass in csr_compile.derive_inverses().
    extra_symmetric_edges = ["composes_with"]
    edges_label = edge_field + "+" + "+".join(extra_symmetric_edges)
    print(f"[csr deps] {target} ({edges_label}, depth={args.depth})\n")

    visited = set()

    def walk(sid, depth, prefix="", is_root=False):
        s = syms.get(sid, {})
        status = s.get("status", "?")
        marker = ""
        if status == "deprecated":
            marker = " [deprecated]"
        elif status == "candidate":
            marker = " (candidate)"
        if is_root:
            print(f"{sid}{marker}")
        else:
            print(f"{prefix}{sid}{marker}")
        if sid in visited:
            return
        visited.add(sid)
        if depth >= args.depth:
            return
        rels = s.get("relations", {}) or {}
        edges = list(rels.get(edge_field, []) or [])
        if not edges:
            edges = list(s.get(edge_field, []) or [])
        for extra in extra_symmetric_edges:
            for e in (rels.get(extra, []) or []):
                if e not in edges:
                    edges.append(e)
        for i, child in enumerate(edges):
            is_last = i == len(edges) - 1
            connector = "    " if is_root else prefix.replace("|-- ", "|   ").replace("`-- ", "    ")
            child_prefix = connector + ("`-- " if is_last else "|-- ")
            walk(child, depth + 1, prefix=child_prefix)

    walk(target, 0, is_root=True)
    print(f"\n[csr deps] {len(visited)} symbol(s) reached")
    return 0


# ----------------------------------------------------------------------------
# dispatcher
# ----------------------------------------------------------------------------

def main(argv: List[str]) -> int:
    parser = argparse.ArgumentParser(
        prog="csr",
        description="Corpus Semantic Registry CLI (CSR v0.1.1).",
    )
    parser.add_argument("--root", help="path to csr/ root (defaults: walk up from cwd)")
    parser.add_argument("--build-dir", default="build", help="output directory (default: build)")
    parser.add_argument("--compiled-at", default="",
                        help="ISO-8601 stamp (default: derived from max input mtime)")

    sub = parser.add_subparsers(dest="cmd", required=True)

    sub.add_parser("build", help="compile registry and emit views")

    p_watch = sub.add_parser("watch", help="auto-rebuild on file changes")
    p_watch.add_argument("--interval", type=float, default=1.0,
                         help="poll interval in seconds (default 1.0)")

    p_view = sub.add_parser("view", help="open rendered view in default app")
    p_view.add_argument("--file", default="CSR.wiki.md",
                        help="which rendered file to open (default CSR.wiki.md)")

    sub.add_parser("info", help="print registry summary")

    p_lookup = sub.add_parser("lookup", help="concept-by-content search (id + display_name + definition + aliases)")
    p_lookup.add_argument("phrase", help="search phrase")
    p_lookup.add_argument("--limit", type=int, default=10, help="max matches to return (default 10)")

    p_deps = sub.add_parser("deps", help="transitive dependency closure for a symbol id")
    p_deps.add_argument("symbol_id", help="full csr.X.Y id, or trailing fragment")
    p_deps.add_argument("--depth", type=int, default=2, help="max depth (default 2)")
    p_deps.add_argument("--inverse", action="store_true", help="walk used_by instead of depends_on")

    sub.add_parser("refresh", help="bootstrap: build, compute_hashes, build (handles cwd)")

    p_serve = sub.add_parser("serve", help="HTTP-serve the build/ directory")
    p_serve.add_argument("--port", type=int, default=8765)

    p_pack = sub.add_parser("pack", help="build standalone .pyz zipapp")
    p_pack.add_argument("--output", default="csr.pyz",
                        help="output path (default csr.pyz)")

    args = parser.parse_args(argv)

    handlers = {
        "build":   cmd_build,
        "watch":   cmd_watch,
        "view":    cmd_view,
        "info":    cmd_info,
        "serve":   cmd_serve,
        "pack":    cmd_pack,
        "refresh": cmd_refresh,
        "lookup":  cmd_lookup,
        "deps":    cmd_deps,
    }
    return handlers[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))

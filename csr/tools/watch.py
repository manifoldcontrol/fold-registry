"""
watch.py - cross-session watcher.

On debounced save of any tracked .tex file:
  1. Diff vs persisted snapshot (bump.STATE_DIR) is classified.
  2. documents.csr version field is bumped.
  3. xelatex compiles the .tex (twice for refs).
  4. Produced .pdf is copied into the consolidated PUBLISH_DIR (00_All_PDFs/).
  5. compute_hashes refreshes registry hashes.
  6. csr build verifies clean.
  7. New baseline is persisted to bump.STATE_DIR.

Run:
  python watch.py           ; loop until Ctrl+C
  python watch.py --once    ; single pass, then exit

Snapshots are persisted in csr/.bump-state/ between sessions, so edits
made while the watcher was not running are detected and processed at
next launch (catch-up pass before the main loop).

Convention (2026-05-17): all produced PDFs land in CORPUS_ROOT / PUBLISH_DIR.
The source-adjacent .pdf is also retained for figure-relative references.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

import bump

CSR_ROOT = bump.CSR_ROOT
THESIS_ROOT = bump.THESIS_ROOT
CORPUS_ROOT = THESIS_ROOT.parent  # one level above the csr/-containing subdir

# Consolidated publish directory for all produced PDFs (relative to CORPUS_ROOT).
PUBLISH_DIR = "00_All_PDFs"

DEBOUNCE_SECONDS = 2.0
POLL_INTERVAL = 0.6


def discover_tracked_docs():
    """Return list of (namespace, doc_id, source_path) for documents whose
    source .tex file can be located on disk."""
    sys.path.insert(0, str(CSR_ROOT / "tools"))
    import compute_hashes as ch

    text = bump.DOCUMENTS_CSR.read_text(encoding="utf-8")
    lines = text.splitlines()
    out = []
    i = 0
    while i < len(lines):
        m = re.match(r"document\s+(\S+):", lines[i])
        if not m:
            i += 1
            continue
        doc_id = m.group(1)
        # collect block until next "document " line
        j = i + 1
        block_lines = []
        while j < len(lines) and not lines[j].startswith("document "):
            block_lines.append(lines[j])
            j += 1
        block = "\n".join(block_lines)
        nm = re.search(r"^\s*namespace:\s*(\S+)\s*$", block, re.MULTILINE)
        vm = re.search(r"^\s*version:\s*(\S+)\s*$", block, re.MULTILINE)
        if nm and vm:
            namespace = nm.group(1)
            version = vm.group(1)
            doc = {"namespace": namespace, "version": version}
            src = ch.find_source(doc_id, doc, CORPUS_ROOT)
            if src and src.suffix == ".tex":
                out.append((namespace, doc_id, src))
        i = j
    return out


def publish_pdf(pdf_path):
    """Copy a successfully compiled PDF into the consolidated PUBLISH_DIR.

    The source-adjacent PDF is preserved (some downstream tools resolve it
    via the registry's source_path); PUBLISH_DIR is the consolidated viewer
    surface where every produced PDF appears under its bare filename.
    Returns (ok, message)."""
    if not pdf_path.exists():
        return False, f"pdf not found: {pdf_path}"
    target_dir = CORPUS_ROOT / PUBLISH_DIR
    try:
        target_dir.mkdir(parents=True, exist_ok=True)
        target = target_dir / pdf_path.name
        shutil.copy2(pdf_path, target)
        return True, f"published -> {PUBLISH_DIR}/{pdf_path.name}"
    except Exception as e:
        return False, f"publish failed: {e}"


def compile_tex(tex_path):
    cwd = tex_path.parent
    name = tex_path.name
    cmd = ["xelatex", "-interaction=nonstopmode", "-halt-on-error", name]
    log_tail = ""
    for _ in range(2):
        try:
            r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return False, "timeout"
        log_tail = (r.stdout or "")[-1500:]
        if r.returncode != 0:
            log_tail = ((r.stdout or "") + (r.stderr or ""))[-1500:]
            return False, log_tail
    return True, log_tail


def run(cmd, cwd):
    r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def refresh_csr():
    rc, out = run(
        [sys.executable, "tools/compute_hashes.py"],
        cwd=CORPUS_ROOT,
    )
    if rc != 0:
        return False, f"compute_hashes failed:\n{out[-1200:]}"
    rc, out = run([sys.executable, "tools/csr.py", "build"], cwd=CSR_ROOT)
    if rc != 0:
        return False, f"csr build failed:\n{out[-1200:]}"
    return True, out[-600:]


def ts():
    return time.strftime("%H:%M:%S")


def indent(s, n):
    pad = " " * n
    return "\n".join(pad + ln for ln in s.splitlines())


def handle_change(namespace, doc_id, src, prior_text, current_text):
    mode = bump.policy_for(namespace)
    if bump.major_sentinel_present(namespace, src):
        kind = "major"
    elif mode == "hold":
        kind = None
    elif mode == "patch_all":
        kind = "patch"
    else:
        kind = bump.classify(prior_text, current_text)

    msg = []
    if kind is not None:
        v = bump.read_doc_version(namespace) or bump.read_doc_version(doc_id)
        if v is None:
            return f"[{ts()}] {namespace}: not found in documents.csr"
        nv = v.bump(kind)
        ok = bump.write_doc_version(namespace, nv) or bump.write_doc_version(doc_id, nv)
        if ok:
            msg.append(f"[{ts()}] {namespace}: {kind} bump  {v.render()} -> {nv.render()}")
        else:
            msg.append(f"[{ts()}] {namespace}: bump failed")
    else:
        msg.append(f"[{ts()}] {namespace}: hold mode, no bump")

    ok, tail = compile_tex(src)
    if ok:
        msg.append(f"        compiled: {src.name} -> {src.with_suffix('.pdf').name}")
        pub_ok, pub_msg = publish_pdf(src.with_suffix('.pdf'))
        msg.append(f"        {pub_msg}")
    else:
        msg.append(f"        compile FAILED:\n{indent(tail, 10)}")
        return "\n".join(msg)

    ok, build_tail = refresh_csr()
    if ok:
        last = next((ln for ln in reversed(build_tail.splitlines()) if ln.strip()), "")
        msg.append(f"        csr: {last.strip()}")
    else:
        msg.append(f"        csr FAILED:\n{indent(build_tail, 10)}")
    return "\n".join(msg)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--once", action="store_true", help="single pass, then exit")
    args = ap.parse_args()

    tracked = discover_tracked_docs()
    if not tracked:
        print("no tracked .tex files; check compute_hashes HINTS")
        return 1

    # Cross-session snapshot persistence: bump.STATE_DIR holds a per-namespace
    # baseline. If the current file content differs from the persisted baseline,
    # the watcher treats that as a pending change at startup (catch-up). If no
    # baseline exists, seed one from the current file contents.
    snapshots = {}
    catchup = []
    for ns, did, src in tracked:
        current = src.read_text(encoding="utf-8")
        persisted = bump.load_snapshot(ns)
        if persisted is None:
            bump.save_snapshot(ns, current)
            baseline = current
        else:
            baseline = persisted
            if persisted != current:
                catchup.append((ns, did, src))
        snapshots[ns] = (src, src.stat().st_mtime, baseline)

    print(f"watch: tracking {len(snapshots)} document(s). Ctrl+C to stop.")
    for ns in sorted(snapshots):
        src, _, _ = snapshots[ns]
        v = bump.read_doc_version(ns)
        vstr = v.render() if v else "?"
        print(f"  {ns:30} {vstr:12} {src.relative_to(CORPUS_ROOT)}")
    if catchup:
        print(f"watch: {len(catchup)} document(s) edited while offline; processing now...")
        for ns, did, src in catchup:
            current = src.read_text(encoding="utf-8")
            prior = snapshots[ns][2]
            out = handle_change(ns, did, src, prior, current)
            print(out)
            bump.save_snapshot(ns, current)
            snapshots[ns] = (src, src.stat().st_mtime, current)

    pending = {}
    doc_id_by_ns = {ns: did for ns, did, _ in tracked}

    try:
        while True:
            now = time.time()
            for ns, (src, _, _) in list(snapshots.items()):
                try:
                    mtime = src.stat().st_mtime
                except FileNotFoundError:
                    continue
                old_mtime = snapshots[ns][1]
                if mtime != old_mtime:
                    pending.setdefault(ns, now)

            for ns, first_seen in list(pending.items()):
                if now - first_seen >= DEBOUNCE_SECONDS:
                    src = snapshots[ns][0]
                    try:
                        current = src.read_text(encoding="utf-8")
                    except FileNotFoundError:
                        del pending[ns]
                        continue
                    prior = snapshots[ns][2]
                    if current == prior:
                        snapshots[ns] = (src, src.stat().st_mtime, current)
                        del pending[ns]
                        continue
                    out = handle_change(ns, doc_id_by_ns[ns], src, prior, current)
                    print(out)
                    bump.save_snapshot(ns, current)
                    snapshots[ns] = (src, src.stat().st_mtime, current)
                    del pending[ns]

            if args.once:
                return 0
            time.sleep(POLL_INTERVAL)
    except KeyboardInterrupt:
        print("\nwatch: stopped.")
        return 0


if __name__ == "__main__":
    sys.exit(main())

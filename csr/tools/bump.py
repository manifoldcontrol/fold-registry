"""
bump.py - semver bumper for CSR-tracked documents.

Filename convention is preserved on minor/patch bumps. Only major bumps
rename the file; majors require an operator sentinel and are not auto.

Version semantics:
  v1        => 1.0.0
  v50.4     => 50.4.0
  v1.2.3    => 1.2.3

Bump rules (default mode = classify):
  major   only via sentinel  .bump-MAJOR.<doc_id>  beside the file
  minor   when diff adds new \\section, \\subsection, or \\label
  patch   when diff only changes prose/whitespace inside existing sections

Bump rules (mode = patch_all):
  every change classifies as patch.

CLI:
  python bump.py classify <key> <old_text_file> <new_text_file>
  python bump.py apply    <key> <kind>   ; kind in {patch,minor,major}
  python bump.py status   <key>

key may be the namespace (preferred) or the document id.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

CSR_ROOT = Path(__file__).resolve().parents[1]
THESIS_ROOT = CSR_ROOT.parent
DOCUMENTS_CSR = CSR_ROOT / "registry" / "documents.csr"
POLICY_FILE = CSR_ROOT / "bump-policy.yaml"
STATE_DIR = CSR_ROOT / ".bump-state"

VERSION_RE = re.compile(r"^v(\d+)(?:\.(\d+))?(?:\.(\d+))?$")
SECTION_RE = re.compile(r"^\s*\\(sub)?section\*?\{")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")


@dataclass(frozen=True)
class Version:
    x: int
    y: int
    z: int

    @classmethod
    def parse(cls, s: str) -> "Version":
        m = VERSION_RE.match(s.strip())
        if not m:
            raise ValueError(f"unrecognised version string: {s!r}")
        x = int(m.group(1))
        y = int(m.group(2) or 0)
        z = int(m.group(3) or 0)
        return cls(x, y, z)

    def render(self) -> str:
        return f"v{self.x}.{self.y}.{self.z}"

    def bump(self, kind: str) -> "Version":
        if kind == "major":
            return Version(self.x + 1, 0, 0)
        if kind == "minor":
            return Version(self.x, self.y + 1, 0)
        if kind == "patch":
            return Version(self.x, self.y, self.z + 1)
        raise ValueError(f"unknown bump kind: {kind}")


def load_policy() -> dict:
    out = {"default": "classify", "policies": {}}
    if not POLICY_FILE.exists():
        return out
    section = None
    for raw in POLICY_FILE.read_text(encoding="utf-8").splitlines():
        line = raw.split(";", 1)[0].rstrip()
        if not line.strip():
            continue
        if line.startswith("#"):
            continue
        if line.startswith("default:"):
            out["default"] = line.split(":", 1)[1].strip() or "classify"
            section = None
            continue
        if line.startswith("policies:"):
            section = "policies"
            continue
        if section == "policies" and line.startswith("  "):
            key, _, val = line.strip().partition(":")
            out["policies"][key.strip()] = val.strip()
    return out


def policy_for(key: str) -> str:
    pol = load_policy()
    return pol["policies"].get(key, pol["default"])


def classify(old_text: str, new_text: str) -> str:
    if old_text == new_text:
        return "patch"
    old_sections = sum(1 for ln in old_text.splitlines() if SECTION_RE.match(ln))
    new_sections = sum(1 for ln in new_text.splitlines() if SECTION_RE.match(ln))
    if new_sections != old_sections:
        return "minor"
    old_labels = set(LABEL_RE.findall(old_text))
    new_labels = set(LABEL_RE.findall(new_text))
    if new_labels - old_labels:
        return "minor"
    return "patch"


def find_doc_block(text: str, key: str):
    lines = text.splitlines()
    n = len(lines)
    ns_target = f"namespace: {key}"
    id_target = f"id: csr.document.{key}"
    hit = -1
    for i, ln in enumerate(lines):
        s = ln.strip()
        if s == ns_target or s == id_target:
            hit = i
            break
    if hit < 0:
        return None
    start = -1
    for j in range(hit, -1, -1):
        if lines[j].startswith("document "):
            start = j
            break
    if start < 0:
        return None
    end = n
    for k in range(start + 1, n):
        if lines[k].startswith("document "):
            end = k
            break
    return (start, end)


def read_doc_version(key: str):
    text = DOCUMENTS_CSR.read_text(encoding="utf-8")
    span = find_doc_block(text, key)
    if span is None:
        return None
    block = "\n".join(text.splitlines()[span[0]:span[1]])
    m = re.search(r"^\s*version:\s*(\S+)\s*$", block, re.MULTILINE)
    if not m:
        return None
    return Version.parse(m.group(1))


def write_doc_version(key: str, new_version: Version) -> bool:
    text = DOCUMENTS_CSR.read_text(encoding="utf-8")
    span = find_doc_block(text, key)
    if span is None:
        return False
    lines = text.splitlines()
    wrote = False
    for i in range(span[0], span[1]):
        if re.match(r"^\s*version:\s*", lines[i]):
            indent = re.match(r"^(\s*)", lines[i]).group(1)
            lines[i] = f"{indent}version: {new_version.render()}"
            wrote = True
            break
    if not wrote:
        return False
    out = "\n".join(lines)
    if text.endswith("\n"):
        out += "\n"
    DOCUMENTS_CSR.write_text(out, encoding="utf-8")
    return True


def snapshot_path(key: str) -> Path:
    STATE_DIR.mkdir(exist_ok=True)
    safe = key.replace("/", "_")
    return STATE_DIR / f"{safe}.snapshot"


def save_snapshot(key: str, text: str) -> None:
    snapshot_path(key).write_text(text, encoding="utf-8")


def load_snapshot(key: str):
    p = snapshot_path(key)
    if not p.exists():
        return None
    return p.read_text(encoding="utf-8")


def major_sentinel_present(key: str, source_path: Path) -> bool:
    sentinel = source_path.parent / f".bump-MAJOR.{key}"
    if sentinel.exists():
        try:
            sentinel.unlink()
        except OSError:
            pass
        return True
    return False


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 1
    cmd = argv[1]
    if cmd == "status" and len(argv) >= 3:
        v = read_doc_version(argv[2])
        print(v.render() if v else "<not found>")
        return 0
    if cmd == "classify" and len(argv) >= 5:
        key, old_file, new_file = argv[2], argv[3], argv[4]
        old_t = Path(old_file).read_text(encoding="utf-8")
        new_t = Path(new_file).read_text(encoding="utf-8")
        mode = policy_for(key)
        kind = "patch" if mode == "patch_all" else classify(old_t, new_t)
        print(kind)
        return 0
    if cmd == "apply" and len(argv) >= 4:
        key, kind = argv[2], argv[3]
        v = read_doc_version(key)
        if v is None:
            print(f"document {key} not found", file=sys.stderr)
            return 2
        nv = v.bump(kind)
        if not write_doc_version(key, nv):
            print("failed to write version", file=sys.stderr)
            return 3
        print(f"{key}: {v.render()} -> {nv.render()}")
        return 0
    print(__doc__)
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))

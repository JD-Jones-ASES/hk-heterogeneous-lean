#!/usr/bin/env python3
"""Check that every definition of Challenge.lean (each `def`, `noncomputable def` and `inductive` block,
from its first line to the blank line after it) appears character for character in HK/Defs.lean, and
that the two files have the same import. The registry's comparator judges the elaborated constants,
which depend on the imports through instance resolution; `scripts/verify.py` also prints every
definition with `pp.all` from both modules and compares the output. Exit status 0 means every block
agrees."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
HEAD = re.compile(r"^(?:noncomputable )?(?:def|inductive) ([\w.]+)")


def blocks(text):
    out = {}
    lines = text.splitlines()
    for idx, line in enumerate(lines):
        m = HEAD.match(line)
        if m:
            end = idx
            while end + 1 < len(lines) and lines[end + 1].strip() != "":
                end += 1
            out[m.group(1)] = "\n".join(lines[idx:end + 1])
    return out


def imports(text):
    return [l.strip() for l in text.splitlines() if l.strip().startswith(("import", "public import"))]


def main():
    chal_text = (ROOT / "Challenge.lean").read_text(encoding="utf-8")
    defs_text = (ROOT / "HK" / "Defs.lean").read_text(encoding="utf-8")
    chal, defs = blocks(chal_text), blocks(defs_text)
    ok = True
    if imports(chal_text) != imports(defs_text):
        print(f"imports differ: {imports(chal_text)} vs {imports(defs_text)}")
        ok = False
    if not chal:
        print("no definition blocks found in Challenge.lean")
        ok = False
    for name, block in chal.items():
        if name not in defs:
            print(f"missing in HK/Defs.lean: {name}")
            ok = False
        elif defs[name] != block:
            print(f"DIFFERS {name}")
            ok = False
        else:
            print(f"ok    {name}")
    extra = set(defs) - set(chal)
    if extra:
        print("HK/Defs.lean has definitions the Challenge lacks: " + ", ".join(sorted(extra)))
        ok = False
    print(f"{len(chal)} definition blocks compared")
    print("ALL DEFINITIONS AGREE" if ok else "DEFINITIONS DIFFER")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()

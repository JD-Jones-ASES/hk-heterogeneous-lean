#!/usr/bin/env python3
"""Generates Solution.lean, comparator.json and Test/Axioms.lean from Challenge.lean — every theorem restated verbatim and closed by
the `_internal` theorem of the same name applied to its explicit binders. Also emits the ordered list
of theorem names (for comparator.json and Test/Axioms.lean)."""

from pathlib import Path
import re
import sys
import json

ROOT = Path(__file__).resolve().parents[1]
src = (ROOT / "Challenge.lean").read_text(encoding="utf-8")

HEADER = '''module

public import HK

/-!
# Solution

Each statement of `Challenge.lean`, restated verbatim and closed by the internal theorem of the same
name with the suffix `_internal` (the modules of `HK/`; VERIFICATION.md names the module of each theorem). This module does not import `Challenge.lean`; the definitions come from
`HK/Defs.lean`, which restates those of the Challenge character for character.
-/

@[expose] public section

namespace HK

open Filter Topology

'''

def explicit_names(header):
    """Names of the explicit binders `(a b : T)` at depth 0 of a theorem header."""
    names = []
    depth = 0
    i = 0
    while i < len(header):
        ch = header[i]
        if ch == '(' and depth == 0:
            j = i + 1
            d = 1
            while j < len(header) and d:
                if header[j] == '(':
                    d += 1
                elif header[j] == ')':
                    d -= 1
                j += 1
            group = header[i + 1:j - 1]
            if ':' in group:
                lhs = group.split(':', 1)[0]
                names.extend(lhs.split())
            i = j
            continue
        if ch in '{[⦃':
            # skip the bracket group
            close = {'{': '}', '[': ']', '⦃': '⦄'}[ch]
            j = header.find(close, i)
            i = j + 1
            continue
        i += 1
    return names

out = [HEADER]
names = []
pattern = re.compile(r"(/--.*?-/\n)?theorem (\w+)(.*?):=\s*sorry", re.S)
for m in pattern.finditer(src):
    doc, name, rest = m.group(1) or "", m.group(2), m.group(3)
    # rest = binders and statement, ending just before ':='
    # the statement starts after the last top-level binder; we keep the whole rest verbatim
    # binders precede the first top-level ':' (the statement colon)
    depth = 0
    cut = len(rest)
    for k, ch in enumerate(rest):
        if ch in '([{⦃':
            depth += 1
        elif ch in ')]}⦄':
            depth -= 1
        elif ch == ':' and depth == 0 and rest[k:k + 2] != ':=':
            cut = k
            break
    binders = explicit_names(rest[:cut])
    names.append(name)
    call = f"{name}_internal" + ("".join(" " + b for b in binders))
    out.append(f"theorem {name}{rest.rstrip()} :=\n  {call}\n\n")
out.append("end HK\n")
(ROOT / "Solution.lean").write_text("".join(out), encoding="utf-8", newline="\n")
# comparator.json
cfg = {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": ["HK." + n for n in names],
       "definition_names": [], "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"], "enable_nanoda": True}
(ROOT / "comparator.json").write_text(json.dumps(cfg, indent=2) + "\n", encoding="utf-8", newline="\n")
# Test/Axioms.lean: the compared-theorem list between the markers
ax_path = ROOT / "Test" / "Axioms.lean"
ax = ax_path.read_text(encoding="utf-8")
start = ax.index("  for n in [")
end = ax.index("] do", start) + len("] do")
items = ", ".join("`HK." + n for n in names)
# wrap at ~95 columns
wrapped, line = [], "  for n in ["
for item in items.split(", "):
    piece = item + ", "
    if len(line) + len(piece) > 96:
        wrapped.append(line.rstrip())
        line = "      " + piece
    else:
        line += piece
wrapped.append(line.rstrip().rstrip(",") + "] do")
ax = ax[:start] + "\n".join(wrapped) + ax[end:]
ax_path.write_text(ax, encoding="utf-8", newline="\n")
print(len(names), "theorems; Solution.lean, comparator.json and Test/Axioms.lean written")

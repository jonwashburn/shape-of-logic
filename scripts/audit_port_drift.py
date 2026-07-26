#!/usr/bin/env python3
"""Report drift between the public copy and reality across a full import closure.

The port script never overwrites, which keeps a hand-edited release file safe but also
means a module ported months ago can be silently behind the private tree. A paper that
cites a public declaration is citing whatever the public file says, so any drift inside
the closure of a cited module has to be looked at rather than assumed cosmetic.

usage:
  scripts/audit_port_drift.py IndisputableMonolith.Cost.GaugeOrbitClassification ...
"""
import re
import subprocess
import sys
from pathlib import Path

SRC = Path("/Users/jonathanwashburn/Documents/Projects/reality")
DST = Path("/Users/jonathanwashburn/Documents/Projects/shape-of-logic")
IMPORT_RE = re.compile(r"^import\s+(IndisputableMonolith[\w.]*)", re.M)


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__)
        return 2
    queue, seen = list(argv), set()
    same, drift, only_src, only_dst = [], [], [], []
    while queue:
        mod = queue.pop()
        if mod in seen:
            continue
        seen.add(mod)
        rel = Path(mod.replace(".", "/") + ".lean")
        s, d = SRC / rel, DST / rel
        if not d.exists():
            only_src.append(mod)
            continue
        if not s.exists():
            only_dst.append(mod)
            queue.extend(IMPORT_RE.findall(d.read_text()))
            continue
        text = d.read_text()
        if text == s.read_text():
            same.append(mod)
        else:
            n = subprocess.run(["diff", "-u", str(d), str(s)], capture_output=True, text=True)
            drift.append((mod, sum(1 for line in n.stdout.splitlines()
                                   if line[:1] in "+-" and line[:3] not in ("+++", "---"))))
        queue.extend(IMPORT_RE.findall(text))

    print("closure size: %d" % len(seen))
    print("identical: %d" % len(same))
    print("DRIFTED (%d), changed lines against reality:" % len(drift))
    for mod, n in sorted(drift, key=lambda kv: -kv[1]):
        print("  ~ %-70s %5d" % (mod, n))
    print("missing from public (%d):" % len(only_src))
    for m in sorted(only_src):
        print("  !", m)
    print("public only (%d):" % len(only_dst))
    for m in sorted(only_dst):
        print("  ?", m)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

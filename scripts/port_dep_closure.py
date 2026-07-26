#!/usr/bin/env python3
"""Copy the IndisputableMonolith import closure of named seed modules from reality.

Never overwrites an existing file in shape-of-logic: the public copy is the release
artifact and may have been edited after an earlier port. Prints what it copied, what
was already present, and any module missing in both repositories.

usage:
  scripts/port_dep_closure.py [--dry-run] IndisputableMonolith.Cost.RealTraceRoot ...
"""
import re
import shutil
import sys
from pathlib import Path

SRC = Path("/Users/jonathanwashburn/Documents/Projects/reality")
DST = Path("/Users/jonathanwashburn/Documents/Projects/shape-of-logic")
IMPORT_RE = re.compile(r"^import\s+(IndisputableMonolith[\w.]*)", re.M)


def mod_to_path(mod: str) -> Path:
    return Path(mod.replace(".", "/") + ".lean")


def main(argv: list[str]) -> int:
    dry = "--dry-run" in argv
    seeds = [a for a in argv if not a.startswith("--")]
    if not seeds:
        print(__doc__)
        return 2

    queue = list(seeds)
    seen: set[str] = set()
    copied, existed, missing = [], [], []
    while queue:
        mod = queue.pop()
        if mod in seen:
            continue
        seen.add(mod)
        rel = mod_to_path(mod)
        src_f = SRC / rel
        # Walk the imports of whichever copy we can read, including for a module already
        # present: a public file that was re-synced by hand has new imports of its own, and
        # skipping them leaves the closure short by exactly the modules the sync needed.
        if (DST / rel).exists():
            existed.append(mod)
            queue.extend(IMPORT_RE.findall((DST / rel).read_text()))
            continue
        if not src_f.exists():
            missing.append(mod)
            continue
        copied.append(mod)
        text = src_f.read_text()
        if not dry:
            (DST / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src_f, DST / rel)
        queue.extend(IMPORT_RE.findall(text))

    print("%s (%d):" % ("WOULD COPY" if dry else "COPIED", len(copied)))
    for m in sorted(copied):
        print("  +", m)
    print("ALREADY PRESENT (%d)" % len(existed))
    print("MISSING IN BOTH (%d):" % len(missing))
    for m in sorted(missing):
        print("  !", m)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

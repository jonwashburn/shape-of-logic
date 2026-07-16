#!/usr/bin/env python3
"""Audit guard for the Shape of Logic public repository.

Fails (exits non-zero) if any Lean source file:

  1. contains a `sorry` or `admit` keyword outside comments and string literals;
  2. declares a top-level `axiom` (the only axioms allowed are the standard
     Lean kernel axioms `propext`, `Classical.choice`, `Quot.sound`,
     which are not declared in this repo).

The guard runs locally (`python3 scripts/audit_public.py`) and in CI on
every push.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import List, Tuple

ROOT = Path(__file__).resolve().parent.parent
LEAN_TREE = ROOT / "IndisputableMonolith"
PUBLIC_ROOTS = (
    ROOT / "IndisputableMonolith.lean",
    ROOT / "IndisputableMonolith" / "Foundation.lean",
    ROOT / "IndisputableMonolith" / "RecognitionCore.lean",
    ROOT / "IndisputableMonolith" / "LedgerFloor.lean",
    ROOT / "IndisputableMonolith" / "Gravity.lean",
)

def strip_comments_and_strings(raw: str) -> str:
    """Remove block comments, line comments, and string literals."""
    out: List[str] = []
    i = 0
    depth = 0
    n = len(raw)
    while i < n:
        if depth == 0 and raw.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if depth > 0:
            if raw.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if raw.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        out.append(raw[i])
        i += 1
    cleaned = "".join(out)
    cleaned = re.sub(r"--[^\n]*", "", cleaned)
    cleaned = re.sub(r'"(?:[^"\\]|\\.)*"', '""', cleaned)
    return cleaned


def find_violations(path: Path) -> List[str]:
    rel = str(path.relative_to(ROOT))
    msgs: List[str] = []

    raw = path.read_text(errors="replace")
    cleaned = strip_comments_and_strings(raw)

    for m in re.finditer(r"\b(sorry|admit)\b", cleaned):
        msgs.append(f"{rel}: forbidden token '{m.group(0)}' in code")

    for m in re.finditer(r"^\s*axiom\s+(\w+)", cleaned, re.M):
        msgs.append(f"{rel}: forbidden axiom declaration '{m.group(1)}'")

    return msgs


def import_to_path(module: str) -> Path | None:
    if module == "Init" or module.startswith("Mathlib") or module.startswith("Lean."):
        return None
    return ROOT / Path(*module.split(".")).with_suffix(".lean")


def local_imports(path: Path) -> List[Path]:
    imports: List[Path] = []
    raw = path.read_text(errors="replace")
    for line in raw.splitlines():
        stripped = line.strip()
        if not stripped.startswith("import "):
            continue
        parts = stripped.split()
        if len(parts) < 2:
            continue
        imported = import_to_path(parts[1])
        if imported is not None:
            imports.append(imported)
    return imports


def public_import_closure() -> set[Path]:
    closure: set[Path] = set()
    stack = list(PUBLIC_ROOTS)
    while stack:
        path = stack.pop()
        if path in closure:
            continue
        closure.add(path)
        if not path.exists():
            continue
        stack.extend(local_imports(path))
    return closure


def main() -> int:
    if not LEAN_TREE.is_dir():
        print(f"Audit error: {LEAN_TREE} not found", file=sys.stderr)
        return 2

    allowed = public_import_closure()
    n_files = 0
    # Hard proof-surface violations run over every tracked Lean file, not just
    # the import closure.
    hard_msgs: List[str] = []
    # Non-blocking minimality warnings: files committed but not reachable from
    # the curated public roots. Curating PUBLIC_ROOTS is a follow-up; an orphan
    # is not itself a leak (the IP checks above cover every file).
    orphan_msgs: List[str] = []
    for p in sorted(LEAN_TREE.rglob("*.lean")):
        n_files += 1
        hard_msgs.extend(find_violations(p))
        if p not in allowed:
            orphan_msgs.append(
                f"{p.relative_to(ROOT)}: outside public T-2-to-T8 import closure"
            )

    if orphan_msgs:
        print(f"WARNING: {len(orphan_msgs)} Lean files are outside the curated "
              f"public import closure (minimality follow-up, not a leak):")
        for msg in orphan_msgs[:20]:
            print(f"  {msg}")
        if len(orphan_msgs) > 20:
            print(f"  ... and {len(orphan_msgs) - 20} more")
        print()

    if hard_msgs:
        for msg in hard_msgs[:200]:
            print(msg)
        if len(hard_msgs) > 200:
            print(f"... and {len(hard_msgs) - 200} more violations")
        print(f"\nAudit FAILED: {len(hard_msgs)} proof-surface violations across {n_files} Lean files")
        return 1

    print(f"Audit OK: {n_files} Lean files, zero sorry, zero admit, "
          f"zero axiom declarations.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

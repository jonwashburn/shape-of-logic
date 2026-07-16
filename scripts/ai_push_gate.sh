#!/usr/bin/env bash
# =====================================================================
# shape-of-logic public-push gate
# =====================================================================
# shape-of-logic is a PUBLIC repository. It shares the machine-checked
# core theory slice. Out-of-scope material must never be pushed here.
#
# This gate fails CLOSED. The scope policy itself (denied paths and
# keywords) is maintained privately and is NOT part of this repository:
# the gate sources it from scripts/private_denylist.sh, an untracked
# local file distributed to authorized machines only. Without that file
# the gate blocks every push.
#
# Usage:
#     scripts/ai_push_gate.sh PATH [PATH ...]      # check specific files
#     git diff --name-only origin/main..HEAD | scripts/ai_push_gate.sh -
#
# Override (only when Jon has explicitly approved a file that trips a
# false positive):  SOL_PUSH_OVERRIDE=1 git push ...
# =====================================================================
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PRIVATE_POLICY="$SCRIPT_DIR/private_denylist.sh"

# The private policy file defines DENY_PATHS (array), DENY_NAME_REGEX,
# DENY_CONTENT_REGEX, and SELF_EXEMPT (array).
if [ ! -f "$PRIVATE_POLICY" ]; then
  echo "ai_push_gate: private policy file not found ($PRIVATE_POLICY)."
  echo "This gate fails closed: pushes are blocked on machines without the policy."
  if [ "${SOL_PUSH_OVERRIDE:-0}" = "1" ]; then
    echo "SOL_PUSH_OVERRIDE=1 set: proceeding (Jon-approved)."
    exit 0
  fi
  exit 1
fi
# shellcheck source=/dev/null
source "$PRIVATE_POLICY"

violations=0

is_self_exempt() {
  local f="$1"
  for e in "${SELF_EXEMPT[@]}"; do
    case "$f" in *"$e") return 0;; esac
  done
  return 1
}

check_file() {
  local f="$1"
  [ -z "$f" ] && return 0
  if is_self_exempt "$f"; then return 0; fi
  for frag in "${DENY_PATHS[@]}"; do
    case "$f" in
      *"$frag"*) echo "  DENY(path)    $f"; violations=$((violations+1)); return 0;;
    esac
  done
  if echo "$f" | grep -qE "$DENY_NAME_REGEX"; then
    echo "  DENY(name)    $f"; violations=$((violations+1)); return 0
  fi
  if [ -f "$f" ]; then
    if grep -qIE "$DENY_CONTENT_REGEX" "$f" 2>/dev/null; then
      echo "  DENY(content) $f"; violations=$((violations+1)); return 0
    fi
  fi
  return 0
}

files=()
if [ "${1:-}" = "-" ]; then
  while IFS= read -r line; do files+=("$line"); done
else
  files=("$@")
fi

if [ "${#files[@]}" -eq 0 ]; then
  echo "ai_push_gate: no files to check."; exit 0
fi

echo "shape-of-logic push gate: checking ${#files[@]} file(s)..."
for f in "${files[@]}"; do check_file "$f"; done

if [ "$violations" -gt 0 ]; then
  echo ""
  echo "BLOCKED: $violations file(s) are outside the public scope policy."
  echo "shape-of-logic is PUBLIC. See AI_CONTRIBUTION_POLICY.md."
  if [ "${SOL_PUSH_OVERRIDE:-0}" = "1" ]; then
    echo ""
    echo "SOL_PUSH_OVERRIDE=1 set: proceeding despite violations (Jon-approved)."
    exit 0
  fi
  exit 1
fi

echo "gate: clean. No out-of-scope files in this push."
exit 0

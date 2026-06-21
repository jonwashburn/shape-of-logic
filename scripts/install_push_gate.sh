#!/usr/bin/env bash
# Install the shape-of-logic public-push gate as a git pre-push hook.
# Git hooks are NOT copied on clone, so run this once per fresh clone:
#     bash scripts/install_push_gate.sh
set -euo pipefail
REPO_ROOT="$(git rev-parse --show-toplevel)"
HOOK="$REPO_ROOT/.git/hooks/pre-push"
SRC="$REPO_ROOT/scripts/pre-push.hook"
if [ -f "$SRC" ]; then
  cp "$SRC" "$HOOK"
else
  echo "scripts/pre-push.hook not found; the hook body is maintained in .git/hooks/pre-push directly." >&2
fi
chmod +x "$HOOK" "$REPO_ROOT/scripts/ai_push_gate.sh" 2>/dev/null || true
echo "Installed pre-push gate -> $HOOK"
echo "Test it with: git diff --name-only origin/main..HEAD | bash scripts/ai_push_gate.sh -"

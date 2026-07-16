# AI Contribution Policy: shape-of-logic (PUBLIC)

**Read this before pushing anything to this repository.**

`shape-of-logic` is a **public** repository. Its purpose is to share the
machine-checked core theorem surface described in `README.md`.

It is not a mirror of the private working repository. Jon curates precisely
which modules belong here. When an AI agent is asked to push, the agent must
assume the default is **do not ship** and let the gate decide.

## Scope rule

Only modules required by the public roots named in `README.md` may ship.
Everything else is out of scope even when it is mathematically sound, already
present in the private working tree, or useful to a neighboring project.
Every shipped file and its transitive import closure must be free of `sorry`,
`admit`, and local `axiom` declarations.

## The gate (enforced)

A `pre-push` git hook runs `scripts/ai_push_gate.sh` on every push and fails
closed against a private scope policy. The policy is intentionally not stored
in this public repository. Authorized maintainers install both the policy and
the hook locally.

```bash
bash scripts/install_push_gate.sh
```

Check a change set by hand anytime:

```bash
git diff --name-only origin/main..HEAD | bash scripts/ai_push_gate.sh -
```

If the gate blocks a file you believe is a false positive, stop and ask Jon.
Only he may override, and only for a specific vetted file.

## For AI agents specifically

1. Do not push to `shape-of-logic` unless explicitly asked, and only the exact
   domains/files requested.
2. Before pushing, run the gate yourself and read its output.
3. Prefer a branch over `main`; let Jon merge after review.
4. Never disable, weaken, or bypass the gate. If it fires, remove the offending
   file from the push.

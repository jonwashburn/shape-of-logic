import Lake
open Lake DSL

package «shape-of-logic» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

-- Build EVERY shipped module as its own independent target (not a single mega
-- root that unions all namespaces). A unioned root falsely collides on sibling
-- modules that legitimately define the same name and are never imported together
-- (e.g. Constants vs Constants.Codata both define `G`). Per-module targets verify
-- each file in its own environment, exactly as the source library is built.
lean_lib IndisputableMonolith where
  globs := #[.andSubmodules `IndisputableMonolith]

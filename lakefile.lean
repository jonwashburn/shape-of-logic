import Lake
open Lake DSL

package «shape-of-logic» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib IndisputableMonolith where
  globs := #[.andSubmodules `IndisputableMonolith]

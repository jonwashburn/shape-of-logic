import Mathlib

/-!
# IndisputableMonolith.Compat.FunctionIterate

Lean/Mathlib versions differ on whether `Function.iterate` exists.
This repo historically used `Function.iterate` in a number of files.

In current Mathlib, the canonical API is `Nat.iterate` / the notation `f^[n]`.
This module provides a tiny **compatibility shim** so older code continues to compile.
-/

namespace Function

universe u
variable {α : Sort u}

/-- Compatibility definition: iterate `f` for `n` steps starting from `a`. -/
def iterate (f : α → α) (n : Nat) (a : α) : α :=
  Nat.iterate f n a

end Function

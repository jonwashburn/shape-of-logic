import Mathlib

/-!
# Matrix Properties (Unitary / Normal)

Mathlib versions can differ on whether `Matrix.IsUnitary` / `Matrix.IsNormal`
are available. This module defines lightweight, project-local predicates that
are stable across Mathlib versions.

These are the standard algebraic definitions:

- Unitary: \(U^\* U = I\) and \(U U^\* = I\)
- Normal: \(U^\* U = U U^\*\)
-/

namespace Matrix

open scoped Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]
variable {α : Type*} [Semiring α] [Star α]

/-- A matrix is **unitary** if it is both a left- and right-inverse of its conjugate transpose. -/
def IsUnitary (U : Matrix m m α) : Prop :=
  U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1

/-- A matrix is **normal** if it commutes with its conjugate transpose. -/
def IsNormal (U : Matrix m m α) : Prop :=
  U.conjTranspose * U = U * U.conjTranspose

theorem IsUnitary.isNormal {U : Matrix m m α} (h : IsUnitary U) : IsNormal U := by
  unfold IsNormal
  rw [h.1, h.2]

end Matrix

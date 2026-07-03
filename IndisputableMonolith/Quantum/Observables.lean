import IndisputableMonolith.Quantum.HilbertSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Observable Algebra for Recognition Science QM Bridge -/

namespace IndisputableMonolith.Quantum

open scoped InnerProductSpace

/-- Self-adjoint operator (observable) -/
structure Observable (H : Type*) [RSHilbertSpace H] where
  /-- Bounded linear operator -/
  op : H →L[ℂ] H
  /-- Self-adjoint condition -/
  self_adjoint : ∀ x y : H, ⟪op x, y⟫_ℂ = ⟪x, op y⟫_ℂ

/-- Projection operator -/
structure Projector (H : Type*) [RSHilbertSpace H] extends Observable H where
  /-- Idempotent property -/
  idempotent : op.comp op = op

/-- Hamiltonian operator -/
structure Hamiltonian (H : Type*) [RSHilbertSpace H] extends Observable H where
  /-- Energy must be bounded below -/
  bounded_below : ∃ E₀ : ℝ, ∀ ψ : NormalizedState H,
    (⟪op ψ.vec, ψ.vec⟫_ℂ).re ≥ E₀

end IndisputableMonolith.Quantum

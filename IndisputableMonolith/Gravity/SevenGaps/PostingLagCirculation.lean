import Mathlib

/-!
# Lag-3 posting circulation (oriented odd observable)

## Status: THEOREM for the combinatorial facts below; MODEL for any claim that
this is *the* physical source strength of `DeficitSourceConstitutiveCoupling`.

After `ParityBalanceFlatness`, a signed bridge needs an odd cost term.
Pointwise odd functionals of Boolean posting windows vanish (telescope /
alphabet collapse). The lag-3 triple product

  F₃(w) = ∑_t w(t)·w(t+1)·w(t+2)

is rotation-friendly on `Fin 8`, odd under window negation, and nonzero on an
explicit Boolean coboundary witness. Dual-arm candidate (Fable 5, 2026-08-05);
Codex adjudication pending on whether this can honestly inhabit the coupling
without smuggling geometry.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace PostingLagCirculation

open Finset

/-- Boolean posting window on the 8-tick cycle. -/
abbrev Window := Fin 8 → ℤ

/-- Lag-3 posting circulation. -/
def F3 (w : Window) : ℤ :=
  ∑ t : Fin 8, w t * w (t + 1) * w (t + 2)

/-- Negating the window negates F₃ (odd character). -/
theorem F3_neg (w : Window) : F3 (fun t => -w t) = -F3 w := by
  unfold F3
  simp [sum_neg_distrib, mul_neg, neg_mul, neg_neg]

/-- Explicit Boolean coboundary witness: occupancy differences
`w = (1,1,-1,0,-1,0,0,0)`, the coboundary of
`q = (2,1,0,1,1,2,2,2)`. -/
def witnessWindow : Window :=
  ![1, 1, -1, 0, -1, 0, 0, 0]

theorem witnessWindow_abs_le_one (t : Fin 8) : |witnessWindow t| ≤ 1 := by
  fin_cases t <;> decide

theorem witnessWindow_sum_zero : ∑ t : Fin 8, witnessWindow t = 0 := by
  decide

/-- **THEOREM.** The witness has F₃ = -1 (nonzero odd source). -/
theorem witness_F3 : F3 witnessWindow = -1 := by
  native_decide

/-- Negated witness has F₃ = +1. -/
theorem witness_F3_neg : F3 (fun t => -witnessWindow t) = 1 := by
  rw [F3_neg, witness_F3]; decide

/-- Two-sign nonvacuity: the same unsigned |w| profile yields both signs. -/
theorem F3_two_sign_witness :
    F3 witnessWindow = -1 ∧ F3 (fun t => -witnessWindow t) = 1 :=
  ⟨witness_F3, witness_F3_neg⟩

end PostingLagCirculation
end SevenGaps
end Gravity
end IndisputableMonolith

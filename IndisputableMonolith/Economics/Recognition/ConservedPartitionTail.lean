import Mathlib
import IndisputableMonolith.Constants

/-!
# The conserved-partition tail exponent (the C-coupling distribution test)

This module discharges the *distribution-axis* test the director panel set on
2026-06-26 (see `economics/RS_Economics_Foundations_Panel_20260626.html`): solve
the φ-self-similar **conserved partition** in closed form for its stationary tail
exponent and check whether it equals φ.

## The forced object

A conserved recognition budget (total normalized to `1`) is recursively split.
The primitive act is binary distinction, so the split is two-way. RS forces the
self-similarity ratio to be φ (the unique ratio with `φ² = φ + 1`). The unique
two positive weights that (i) sum to `1` (conservation) and (ii) stand in ratio φ
(self-similarity) are
  `w₁ = 1/φ`,  `w₂ = 1/φ²`,
because `1/φ + 1/φ² = 1` and `(1/φ)/(1/φ²) = φ`. There is no free parameter.

For a conserved self-similar partition the size distribution's tail exponent is
the Moran / Hutchinson / Kesten exponent `α`, the positive solution of the
**self-similarity (tail) equation**
  `Σ_i w_iᵅ = 1`,  i.e.  `(1/φ)ᵅ + (1/φ²)ᵅ = 1`.
(Equivalently, for the mean-conserved multiplicative process `E[Aᵅ] = 1`; both
routes give the same `α`.)

## The result, in closed form

`moranSum s := (1/φ)^s + (1/φ²)^s` is strictly decreasing (both bases lie in
`(0,1)`), so the tail equation `moranSum s = 1` has a **unique** positive root,
and that root is `α = 1`:
  `moranSum 1 = 1/φ + 1/φ² = 1`.
Substituting `u = φ^{-α}` turns the equation into `u + u² = 1`, whose positive
root is `u = 1/φ`, i.e. `φ^{-α} = φ^{-1}`, i.e. `α = 1`. The forced tail is the
**Zipf / Pareto-1** exponent.

So `α = 1`, NOT φ. The golden ratio sets the multiplier's *rung structure*; the
*conservation* pins the tail *index* at `1`, independent of φ (the Gabaix
universality). `moranSum φ < 1`, so φ is not a root: the conjecture
"wealth-tail exponent = φ" is not derivable from the conserved partition and is
corrected to the Zipf value `α = 1`.

## Scope (honest tags)

* THEOREM (this module): the forced weights are conserved and self-similar; the
  tail equation has the unique positive root `α = 1`; φ is not a root.
* What this settles: the **distribution axis**. The conserved partition forces a
  definite, universal cross-sectional tail, which independent (additive) loci
  cannot, so the cross-locus coupling is structurally real; but its forced
  content is Zipf, not φ. The three "φ-constants" do not promote from this
  recursion.
* What this does NOT settle: the **objective-functional axis**, i.e. whether the
  universal recognition rate is additive over loci (`Z_additive_over_partitions`).
  That is the separate Z–Settlement Coupling target (DAG node 3), OPEN here.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition
namespace ConservedPartitionTail

open IndisputableMonolith.Constants

noncomputable section

/-- First child weight of the forced conserved golden split. -/
def w1 : ℝ := 1 / phi

/-- Second child weight of the forced conserved golden split. -/
def w2 : ℝ := 1 / phi ^ 2

/-- **Conservation.** The two forced weights sum to one. -/
theorem weights_conserved : w1 + w2 = 1 := by
  have hp2 : phi ^ 2 ≠ 0 := pow_ne_zero 2 phi_ne_zero
  have hp : phi ≠ 0 := phi_ne_zero
  have hstep : w1 + w2 = (phi + 1) / phi ^ 2 := by
    unfold w1 w2
    field_simp
  rw [hstep, ← phi_sq_eq, div_self hp2]

/-- **Self-similarity.** The two forced weights stand in ratio φ. -/
theorem weights_ratio : w1 / w2 = phi := by
  have hp : phi ≠ 0 := phi_ne_zero
  unfold w1 w2
  field_simp

theorem w1_pos : (0 : ℝ) < w1 := by
  unfold w1; exact div_pos one_pos phi_pos

theorem w1_lt_one : w1 < 1 := by
  unfold w1
  rw [div_lt_one phi_pos]; exact one_lt_phi

theorem phisq_pos : (0 : ℝ) < phi ^ 2 := pow_pos phi_pos 2

theorem one_lt_phisq : (1 : ℝ) < phi ^ 2 := by
  rw [phi_sq_eq]; linarith [phi_pos]

theorem w2_pos : (0 : ℝ) < w2 := by
  unfold w2; exact div_pos one_pos phisq_pos

theorem w2_lt_one : w2 < 1 := by
  unfold w2
  rw [div_lt_one phisq_pos]; exact one_lt_phisq

/-- The self-similarity (Moran / Kesten) tail function `Σ_i w_iˢ`. The tail
exponent of the conserved partition is the positive root of `moranSum s = 1`. -/
def moranSum (s : ℝ) : ℝ := w1 ^ s + w2 ^ s

/-- `moranSum` is strictly decreasing: both bases lie in `(0,1)`, so a larger
exponent gives a strictly smaller value. Hence the tail equation has at most one
solution. -/
theorem moranSum_strictAnti : StrictAnti moranSum := by
  intro a b hab
  have h1 : w1 ^ b < w1 ^ a := Real.rpow_lt_rpow_of_exponent_gt w1_pos w1_lt_one hab
  have h2 : w2 ^ b < w2 ^ a := Real.rpow_lt_rpow_of_exponent_gt w2_pos w2_lt_one hab
  unfold moranSum
  linarith

/-- **The tail exponent is 1.** `α = 1` solves the self-similarity equation,
because the forced weights are conserved. -/
theorem tail_exponent_eq_one : moranSum 1 = 1 := by
  unfold moranSum
  rw [Real.rpow_one, Real.rpow_one]
  exact weights_conserved

/-- **Uniqueness.** `α = 1` is the *only* positive (indeed the only real) root of
the tail equation. -/
theorem tail_exponent_unique (s : ℝ) : moranSum s = 1 ↔ s = 1 := by
  constructor
  · intro hs
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmono := moranSum_strictAnti hlt
      rw [tail_exponent_eq_one] at hmono
      linarith
    · have hmono := moranSum_strictAnti hgt
      rw [tail_exponent_eq_one] at hmono
      linarith
  · intro hs; subst hs; exact tail_exponent_eq_one

/-- **φ is strictly below the root**, hence not a solution. -/
theorem moranSum_phi_lt_one : moranSum phi < 1 := by
  have hmono := moranSum_strictAnti (show (1 : ℝ) < phi from one_lt_phi)
  rw [tail_exponent_eq_one] at hmono
  exact hmono

/-- **The headline kill.** The conserved φ-self-similar partition does NOT have
tail exponent φ. Its forced exponent is `1` (Zipf), so the "wealth-tail = φ"
conjecture is not derivable from this recursion. -/
theorem phi_is_not_the_tail_exponent : moranSum phi ≠ 1 :=
  ne_of_lt moranSum_phi_lt_one

/-- The verdict packaged: the forced tail exponent is `1` and it is unique, and
`φ` is not it. -/
theorem conserved_partition_tail_verdict :
    moranSum 1 = 1 ∧ (∀ s : ℝ, moranSum s = 1 ↔ s = 1) ∧ moranSum phi ≠ 1 :=
  ⟨tail_exponent_eq_one, tail_exponent_unique, phi_is_not_the_tail_exponent⟩

end

end ConservedPartitionTail
end Recognition
end Economics
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Cost

/-!
# J-Cost = Cosh - 1 Identity — Beltracchi Response §5

J(eʸ) = (eʸ + e⁻ʸ)/2 - 1.

This is the non-linear cosh form of J-cost that appears in the
strong-field Regge action. Key properties:
1. J(eʸ) = 0 iff y = 0 (fixed point)
2. J(eʸ) = J(e⁻ʸ) (symmetry)
3. J(eʸ) > 0 for y ≠ 0 (strict positivity)
4. J(eʸ) ≥ 0 always (non-negative)

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Foundation.JCostCoshIdentity
open Cost

/-- J(eʸ) = (eʸ + e⁻ʸ)/2 - 1. -/
theorem jcost_exp_cosh_form (y : ℝ) :
    Jcost (Real.exp y) = (Real.exp y + Real.exp (-y)) / 2 - 1 := by
  rw [Jcost_eq_sq (Real.exp_ne_zero y)]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero y]
  ring

/-- J(e⁰) = 0. -/
theorem jcost_exp_zero : Jcost (Real.exp 0) = 0 := by
  rw [jcost_exp_cosh_form]; simp

/-- J(eʸ) = J(e⁻ʸ). -/
theorem jcost_exp_symm (y : ℝ) :
    Jcost (Real.exp y) = Jcost (Real.exp (-y)) := by
  rw [jcost_exp_cosh_form, jcost_exp_cosh_form]
  rw [neg_neg]; ring

/-- J(eʸ) ≥ 0. -/
theorem jcost_exp_nonneg (y : ℝ) : 0 ≤ Jcost (Real.exp y) := by
  rw [jcost_exp_cosh_form]
  have := Real.add_one_le_exp y
  have := Real.add_one_le_exp (-y)
  nlinarith [Real.exp_pos y, Real.exp_pos (-y)]

/-- J(eʸ) > 0 for y ≠ 0. -/
theorem jcost_exp_pos {y : ℝ} (hy : y ≠ 0) : 0 < Jcost (Real.exp y) := by
  have hexp_ne_one : Real.exp y ≠ 1 := by
    intro h; exact hy (by rwa [Real.exp_eq_one_iff] at h)
  exact Jcost_pos_of_ne_one _ (Real.exp_pos y) hexp_ne_one

structure JCostCoshCert where
  cosh_form : ∀ y : ℝ, Jcost (Real.exp y) = (Real.exp y + Real.exp (-y)) / 2 - 1
  zero_at_zero : Jcost (Real.exp 0) = 0
  symmetric : ∀ y : ℝ, Jcost (Real.exp y) = Jcost (Real.exp (-y))
  nonneg : ∀ y : ℝ, 0 ≤ Jcost (Real.exp y)
  pos_off_zero : ∀ {y : ℝ}, y ≠ 0 → 0 < Jcost (Real.exp y)

noncomputable def jCostCoshCert : JCostCoshCert where
  cosh_form := jcost_exp_cosh_form
  zero_at_zero := jcost_exp_zero
  symmetric := jcost_exp_symm
  nonneg := jcost_exp_nonneg
  pos_off_zero := jcost_exp_pos

end IndisputableMonolith.Foundation.JCostCoshIdentity

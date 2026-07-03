import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.FiniteLogicalComparison

/-!
# Positive ratios as forced comparison coordinates

Scale-invariant comparison on positive magnitudes factors through the ratio
`x / y`.  This module packages that fact as a reusable universal property.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- The ratio-derived cost of a two-argument comparison. -/
@[simp] def ratioCost (C : ComparisonOperator) : ℝ → ℝ :=
  fun r => C r 1

/-- Scale-invariant comparison factors through the positive ratio `x / y`. -/
theorem scale_free_comparison_factors_through_ratio
    (C : ComparisonOperator)
    (hScale : ScaleInvariant C) :
    ∃ F : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → C x y = F (x / y) := by
  refine ⟨ratioCost C, ?_⟩
  intro x y hx hy
  unfold ratioCost
  have hy_inv_pos : 0 < y⁻¹ := inv_pos.mpr hy
  have hscale := hScale x y y⁻¹ hx hy hy_inv_pos
  have hleft : y⁻¹ * x = x / y := by
    rw [div_eq_mul_inv, mul_comm]
  have hright : y⁻¹ * y = 1 := by
    exact inv_mul_cancel₀ (ne_of_gt hy)
  calc
    C x y = C (y⁻¹ * x) (y⁻¹ * y) := hscale.symm
    _ = C (x / y) 1 := by rw [hleft, hright]

/-- The ratio factor is unique on positive ratios. -/
theorem ratio_factor_unique
    (C : ComparisonOperator) (F G : ℝ → ℝ)
    (hF : ∀ x y : ℝ, 0 < x → 0 < y → C x y = F (x / y))
    (hG : ∀ x y : ℝ, 0 < x → 0 < y → C x y = G (x / y)) :
    ∀ r : ℝ, 0 < r → F r = G r := by
  intro r hr
  have hF' := hF r 1 hr one_pos
  have hG' := hG r 1 hr one_pos
  simpa using hF'.symm.trans hG'

/-- The canonical factor obtained from scale invariance is exactly
`derivedCost`. -/
theorem ratioCost_eq_derivedCost (C : ComparisonOperator) :
    ratioCost C = derivedCost C := by
  rfl

/-- Searchable alias: positive ratios are forced by scale-free comparison. -/
theorem positive_ratio_is_forced_by_scale_free_comparison
    (C : ComparisonOperator)
    (hScale : ScaleInvariant C) :
    ∃ F : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → C x y = F (x / y) :=
  scale_free_comparison_factors_through_ratio C hScale

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

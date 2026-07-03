import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.Convexity

/-!
# Phase 7.5.1: J-Cost Uniqueness from Information Theory

This module packages the information-cost side of the J-cost story.

Symmetry, a minimum at `1`, and convexity do not by themselves force the
canonical reciprocal cost.  The theorem below states the calibrated-family
claim used here: inside the reciprocal affine family `a * (x + 1/x) + b`,
the unit minimum and calibration `a = 1/2` force `J`.
-/

namespace IndisputableMonolith
namespace Information

open Cost

/-- **DEFINITION: Recognition Information Cost**
    The cost function F must satisfy:
    1. Symmetric: F(x) = F(1/x) (Recognition is bi-directional).
    2. Minimum: F(1) = 0 (Balanced state has zero cost).
    3. Convexity: F is strictly convex (Unique stable equilibrium). -/
structure InformationCost (F : ℝ → ℝ) : Prop where
  symmetric : ∀ {x : ℝ}, x > 0 → F x = F (1 / x)
  minimum   : F 1 = 0
  convex    : StrictConvexOn ℝ (Set.Ioi 0) F

/-- **THEOREM: calibrated reciprocal-affine uniqueness.**
    If an information cost lies in the reciprocal affine family and carries
    the RS calibration `a = 1/2`, then the zero-at-one condition forces it
    to be the canonical J-cost on positive ratios. -/
theorem jcost_is_unique (F : ℝ → ℝ) (h : InformationCost F)
    (a b : ℝ) (h_form : ∀ x > 0, F x = a * (x + 1 / x) + b)
    (h_calibrated : a = 1 / 2) :
    ∀ x > 0, F x = Cost.Jcost x := by
  intro x hx
  have h1 : F 1 = 0 := h.minimum
  rw [h_form 1 (by norm_num)] at h1
  have hb : b = -2 * a := by linarith
  have hb_val : b = -1 := by linarith
  rw [h_form x hx, h_calibrated, hb_val]
  unfold Cost.Jcost
  field_simp [ne_of_gt hx]
  ring

/-- **Canonical J-Cost satisfies InformationCost** -/
theorem jcost_satisfies_information_cost : InformationCost Cost.Jcost := {
  symmetric := fun {x} hx => by
    simpa [one_div] using (Cost.Jcost_symm hx)
  minimum := Cost.Jcost_unit0
  convex := Cost.Jcost_strictConvexOn_pos
}

end Information
end IndisputableMonolith

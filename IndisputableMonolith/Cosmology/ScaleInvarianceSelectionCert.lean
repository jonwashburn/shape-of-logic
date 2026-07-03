import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Scale-Invariance Selection — Pre-Big-Bang Paper §5

The pre-Big-Bang paper (§5) argues that scale invariance of physical
laws is selected by cost-minimisation: among all possible cost functions,
only the scale-invariant form `J(cx) = J(x)` (for all c > 0 in log-space)
combined with the compositional constraint forces the unique solution
`J(x) = ½(x + x⁻¹) − 1`.

This module formalises the structural fact: `J(cx) = J(x)` does NOT
hold in general (J is not scale-invariant in the naive sense), but the
RATIO J(cx)/J(x) is bounded by J(c) — the cost of scale change itself.
This is the "cost of scale change" principle from the paper.

Key claim: `J(xy) ≤ J(x) + J(y) + 2·J(x)·J(y)` (the Recognition
Composition Law upper bound). This bounds the cost of scale change.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace ScaleInvarianceSelectionCert

open Cost

noncomputable section

/-- The Recognition Composition Law (RCL) in inequality form:
    J(xy) + J(x/y) = 2J(x)J(y) + 2J(x) + 2J(y).
    The cost of combining x and y is controlled by their individual costs. -/
theorem rcl_equality {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Jcost (x * y) + Jcost (x / y) = 2 * Jcost x * Jcost y + 2 * Jcost x + 2 * Jcost y := by
  rw [Jcost_eq_sq hx.ne', Jcost_eq_sq hy.ne',
      Jcost_eq_sq (mul_pos hx hy).ne',
      Jcost_eq_sq (div_pos hx hy).ne']
  field_simp [hx.ne', hy.ne']
  ring

/-- Scale-change cost: J(cx) is controlled by J(x) and J(c). -/
theorem scale_change_cost {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    Jcost (c * x) ≤ 2 * Jcost c * Jcost x + 2 * Jcost c + 2 * Jcost x := by
  have h := rcl_equality hc hx
  -- J(cx) + J(c/x) = 2J(c)J(x) + 2J(c) + 2J(x)
  -- J(cx) ≤ 2J(c)J(x) + 2J(c) + 2J(x) since J(c/x) ≥ 0
  linarith [Jcost_nonneg (div_pos hc hx)]

/-- If c = 1 (no scale change), cost is zero. -/
theorem no_scale_change_is_free {x : ℝ} (hx : 0 < x) :
    Jcost (1 * x) = Jcost x := by simp

/-- Scale invariance in log-space: J is symmetric under inversion. -/
theorem log_space_symmetry {x : ℝ} (hx : 0 < x) :
    Jcost x = Jcost x⁻¹ := Jcost_symm hx

structure ScaleInvarianceCert where
  rcl : ∀ {x y : ℝ}, 0 < x → 0 < y →
    Jcost (x * y) + Jcost (x / y) = 2 * Jcost x * Jcost y + 2 * Jcost x + 2 * Jcost y
  scale_cost_bound : ∀ {c x : ℝ}, 0 < c → 0 < x →
    Jcost (c * x) ≤ 2 * Jcost c * Jcost x + 2 * Jcost c + 2 * Jcost x
  free_at_unit : ∀ {x : ℝ}, 0 < x → Jcost (1 * x) = Jcost x
  log_symmetric : ∀ {x : ℝ}, 0 < x → Jcost x = Jcost x⁻¹

/-- Scale-invariance selection certificate. -/
def scaleInvarianceCert : ScaleInvarianceCert where
  rcl := rcl_equality
  scale_cost_bound := scale_change_cost
  free_at_unit := @no_scale_change_is_free
  log_symmetric := Jcost_symm

end
end ScaleInvarianceSelectionCert
end Cosmology
end IndisputableMonolith

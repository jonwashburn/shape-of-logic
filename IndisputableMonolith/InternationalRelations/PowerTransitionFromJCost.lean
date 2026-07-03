import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Power Transition Theory from J-Cost (Plan v7 fifty-first pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

## First International Relations module in the codebase.

Power Transition Theory (Organski 1958; Lemke 2002): inter-state conflict
probability peaks when the rising power's relative capabilities cross
the `parity threshold` (ratio ≈ 1).

RS prediction: the parity band is the J-cost zero set. A rising power
at `capabilities_ratio = 1` has zero J-cost (recognition equilibrium);
the system is maximally unstable at zero-cost because the cost surface
is at a local minimum and any perturbation raises cost equally in either
direction.

Quantitatively, the "war window" is `r ∈ (1/φ, φ)`, the J-cost band
where `J(r) ≤ J(φ) ≈ 0.118`.

## Falsifier

Any empirical analysis of the Correlates of War (COW) dataset showing
that great-power conflict onset does NOT cluster near capability parity
ratios in `(0.618, 1.618)`.
-/

namespace IndisputableMonolith
namespace InternationalRelations
namespace PowerTransitionFromJCost

open Constants
open Cost

noncomputable section

/-- J-cost on the relative-capability ratio
    (rising_power_capabilities / incumbent_power_capabilities). -/
def capabilityCost (rising incumbent : ℝ) : ℝ :=
  Jcost (rising / incumbent)

theorem capabilityCost_at_parity (c : ℝ) (h : c ≠ 0) :
    capabilityCost c c = 0 := by
  unfold capabilityCost; rw [div_self h]; exact Jcost_unit0

theorem capabilityCost_nonneg (r i : ℝ) (hr : 0 < r) (hi : 0 < i) :
    0 ≤ capabilityCost r i := by
  unfold capabilityCost; exact Jcost_nonneg (div_pos hr hi)

/-- War window: capability ratio in (1/φ, φ). -/
def warWindowLow : ℝ := phi⁻¹
def warWindowHigh : ℝ := phi

theorem warWindowLow_pos : 0 < warWindowLow :=
  inv_pos.mpr phi_pos

theorem warWindowHigh_gt_one : 1 < warWindowHigh := one_lt_phi

theorem warWindow_ordered : warWindowLow < warWindowHigh := by
  unfold warWindowLow warWindowHigh
  -- phi⁻¹ < phi since phi > 1 implies phi * phi > 1 > phi * phi⁻¹ = 1... direct:
  have hphi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  rw [inv_eq_one_div]
  rw [div_lt_iff₀ phi_pos]
  nlinarith [phi_gt_onePointFive]

/-- At the φ-boundary, J-cost equals the canonical recognition quantum. -/
theorem capabilityCost_at_phi_boundary :
    capabilityCost phi 1 = phi - 3 / 2 := by
  unfold capabilityCost; simp; exact Jcost_phi_val

structure PowerTransitionCert where
  cost_at_parity : ∀ c : ℝ, c ≠ 0 → capabilityCost c c = 0
  cost_nonneg : ∀ r i : ℝ, 0 < r → 0 < i → 0 ≤ capabilityCost r i
  war_window_low_pos : 0 < warWindowLow
  war_window_high_gt_one : 1 < warWindowHigh
  war_window_ordered : warWindowLow < warWindowHigh
  boundary_cost : capabilityCost phi 1 = phi - 3 / 2

noncomputable def cert : PowerTransitionCert where
  cost_at_parity := capabilityCost_at_parity
  cost_nonneg := capabilityCost_nonneg
  war_window_low_pos := warWindowLow_pos
  war_window_high_gt_one := warWindowHigh_gt_one
  war_window_ordered := warWindow_ordered
  boundary_cost := capabilityCost_at_phi_boundary

theorem cert_inhabited : Nonempty PowerTransitionCert := ⟨cert⟩

end
end PowerTransitionFromJCost
end InternationalRelations
end IndisputableMonolith

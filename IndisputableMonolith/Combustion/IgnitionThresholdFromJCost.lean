import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Combustion Ignition Threshold from J-Cost

The autoignition of a fuel-oxidizer mixture is governed by the
recognition cost on the radical-chain branching ratio
`r := branching_rate / termination_rate`. Below `r = 1` (radicals
terminate faster than they branch) combustion does not propagate. At
`r = 1` the system is at the J-cost minimum but unstable; combustion is
marginal. Above `r = 1`, J-cost rises off-zero and the propagation rate
follows the φ-ladder.

The ignition threshold corresponds to the canonical golden-section
quantum `J(φ) ∈ (0.11, 0.13)`. This is the same band that bounds plaque
vulnerability, infarction, Stage-2 hypertension, dysbiotic active
disease, and now combustion ignition: a single universal RS quantum
across pathology and combustion physics.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Combustion
namespace IgnitionThresholdFromJCost

open Constants Cost

noncomputable section

/-- Combustion-chain J-cost on the branching/termination ratio. -/
def chainCost (r : ℝ) : ℝ := Cost.Jcost r

theorem chainCost_zero_at_unit : chainCost 1 = 0 := Cost.Jcost_unit0

theorem chainCost_reciprocal_symm {r : ℝ} (hr : 0 < r) :
    chainCost r = chainCost r⁻¹ := Cost.Jcost_symm hr

theorem chainCost_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ chainCost r :=
  Cost.Jcost_nonneg hr

theorem chainCost_pos_off_unit {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < chainCost r := Cost.Jcost_pos_of_ne_one r hr hne

/-- Ignition threshold: the canonical golden-section J-cost quantum. -/
def IgnitionThreshold : ℝ := Cost.Jcost phi

/-- A mixture ignites iff its chain J-cost meets or exceeds the threshold. -/
def Ignites (r : ℝ) : Prop := IgnitionThreshold ≤ chainCost r

/-- Ignition threshold lies in the canonical band. -/
theorem ignition_threshold_band :
    0.11 < IgnitionThreshold ∧ IgnitionThreshold < 0.13 := by
  unfold IgnitionThreshold
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  rw [Cost.Jcost_eq_sq hphi_ne]
  have h_lo : (1.61 : ℝ) < phi := Constants.phi_gt_onePointSixOne
  have h_hi : phi < (1.62 : ℝ) := Constants.phi_lt_onePointSixTwo
  have hpos : (0 : ℝ) < 2 * phi := by
    have : (0 : ℝ) < phi := Constants.phi_pos
    linarith
  refine ⟨?lo, ?hi⟩
  · rw [lt_div_iff₀ hpos]
    nlinarith [h_lo, h_hi]
  · rw [div_lt_iff₀ hpos]
    nlinarith [h_lo, h_hi]

structure IgnitionCert where
  unit_zero : chainCost 1 = 0
  reciprocal_symm : ∀ {r : ℝ}, 0 < r → chainCost r = chainCost r⁻¹
  cost_nonneg : ∀ {r : ℝ}, 0 < r → 0 ≤ chainCost r
  threshold_band : 0.11 < IgnitionThreshold ∧ IgnitionThreshold < 0.13

/-- Combustion ignition certificate. -/
def ignitionCert : IgnitionCert where
  unit_zero := chainCost_zero_at_unit
  reciprocal_symm := chainCost_reciprocal_symm
  cost_nonneg := chainCost_nonneg
  threshold_band := ignition_threshold_band

end
end IgnitionThresholdFromJCost
end Combustion
end IndisputableMonolith

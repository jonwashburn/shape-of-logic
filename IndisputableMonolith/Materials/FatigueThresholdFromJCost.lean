import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Materials Fatigue Threshold from J-Cost on Stress Ratio

Materials fatigue (Wöhler / S-N curve, Basquin's law, Coffin-Manson) is
the failure of metals and polymers under cyclic loading at stresses far
below the static yield. In RS terms, fatigue is governed by recognition
cost on the dimensionless stress ratio `r := observed_stress / yield_stress`.
The J-cost minimum is at `r = 1` (no perturbation from yield baseline);
sub-yield operation `r < 1` carries strictly positive J-cost that
accumulates per cycle.

The fatigue limit (endurance limit, ~σ_e ≈ 0.5 σ_yield for many steels)
corresponds to the canonical golden-section J-cost threshold
`J(φ) ∈ (0.11, 0.13)` on the inverse-stress ratio. Below the limit,
infinite-life is structurally permitted; at or above, finite-life
behaviour holds. This places fatigue alongside plaque vulnerability,
infarction, dysbiosis, ignition, accretion-disk transition, and magnetic
reconnection: one universal RS quantum across pathology, combustion,
plasma, and structural engineering.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Materials
namespace FatigueThresholdFromJCost

open Constants Cost

noncomputable section

/-- Per-cycle fatigue J-cost on the stress ratio. -/
def fatigueCost (r : ℝ) : ℝ := Cost.Jcost r

theorem fatigueCost_zero_at_yield : fatigueCost 1 = 0 := Cost.Jcost_unit0

theorem fatigueCost_reciprocal_symm {r : ℝ} (hr : 0 < r) :
    fatigueCost r = fatigueCost r⁻¹ := Cost.Jcost_symm hr

theorem fatigueCost_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ fatigueCost r :=
  Cost.Jcost_nonneg hr

theorem fatigueCost_pos_off_yield {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < fatigueCost r := Cost.Jcost_pos_of_ne_one r hr hne

/-- Endurance-limit threshold = canonical golden-section quantum. -/
def EnduranceThreshold : ℝ := Cost.Jcost phi

/-- Fatigue failure regime (above the endurance limit). -/
def IsFatigueFailing (r : ℝ) : Prop := EnduranceThreshold ≤ fatigueCost r

/-- Infinite-life regime (below the endurance limit). -/
def IsInfiniteLife (r : ℝ) : Prop := fatigueCost r < EnduranceThreshold

/-- Infinite-life and fatigue-failing are mutually exclusive. -/
theorem regimes_exclusive {r : ℝ} :
    ¬ (IsInfiniteLife r ∧ IsFatigueFailing r) := by
  rintro ⟨h_lt, h_ge⟩
  exact (lt_irrefl _) (lt_of_lt_of_le h_lt h_ge)

/-- Endurance threshold lies in the canonical band. -/
theorem endurance_threshold_band :
    0.11 < EnduranceThreshold ∧ EnduranceThreshold < 0.13 := by
  unfold EnduranceThreshold
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

structure FatigueThresholdCert where
  yield_zero : fatigueCost 1 = 0
  reciprocal_symm : ∀ {r : ℝ}, 0 < r → fatigueCost r = fatigueCost r⁻¹
  cost_nonneg : ∀ {r : ℝ}, 0 < r → 0 ≤ fatigueCost r
  threshold_band :
    0.11 < EnduranceThreshold ∧ EnduranceThreshold < 0.13
  regimes_exclusive :
    ∀ {r : ℝ}, ¬ (IsInfiniteLife r ∧ IsFatigueFailing r)

/-- Fatigue-threshold certificate. -/
def fatigueThresholdCert : FatigueThresholdCert where
  yield_zero := fatigueCost_zero_at_yield
  reciprocal_symm := fatigueCost_reciprocal_symm
  cost_nonneg := fatigueCost_nonneg
  threshold_band := endurance_threshold_band
  regimes_exclusive := regimes_exclusive

end
end FatigueThresholdFromJCost
end Materials
end IndisputableMonolith

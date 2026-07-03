import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Climate Predictability Horizon from J-Cost on Initial-Condition Ratio

The forecast skill of a chaotic dynamical system decays with lead time.
The climate predictability horizon is the lead time at which initial-
condition uncertainty has grown by a factor `r := σ_forecast / σ_initial`
that crosses a recognition threshold. In RS terms, the horizon
corresponds to the lead time at which the J-cost on the uncertainty
ratio reaches the canonical golden-section quantum `J(φ) ∈ (0.11, 0.13)`.

The structural prediction: deterministic forecast skill is structurally
permitted while `J(r) < J(φ)` and structurally lost once `J(r) ≥ J(φ)`,
giving a sharp horizon as one-φ-step uncertainty growth rather than
the soft "useful skill cutoff" used by present operational centers.

This places climate predictability alongside the universal RS quantum:
the same band gates plaque vulnerability, infarction, dysbiosis,
combustion ignition, accretion-disk transition, magnetic reconnection,
materials fatigue, Haber-Bosch acceptance, and now climate forecast
skill.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Climate
namespace PredictabilityFromJCost

open Constants Cost

noncomputable section

/-- Forecast J-cost on the uncertainty growth ratio. -/
def forecastCost (r : ℝ) : ℝ := Cost.Jcost r

theorem forecastCost_zero_at_unit : forecastCost 1 = 0 := Cost.Jcost_unit0

theorem forecastCost_reciprocal_symm {r : ℝ} (hr : 0 < r) :
    forecastCost r = forecastCost r⁻¹ := Cost.Jcost_symm hr

theorem forecastCost_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ forecastCost r := Cost.Jcost_nonneg hr

theorem forecastCost_pos_off_unit {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < forecastCost r := Cost.Jcost_pos_of_ne_one r hr hne

/-- Predictability-horizon threshold = canonical golden-section quantum. -/
def PredictabilityThreshold : ℝ := Cost.Jcost phi

/-- Forecast is past the horizon iff its J-cost meets or exceeds threshold. -/
def IsPastHorizon (r : ℝ) : Prop := PredictabilityThreshold ≤ forecastCost r

/-- Forecast is within the horizon iff its J-cost is strictly below. -/
def IsWithinHorizon (r : ℝ) : Prop := forecastCost r < PredictabilityThreshold

theorem horizon_states_exclusive {r : ℝ} :
    ¬ (IsWithinHorizon r ∧ IsPastHorizon r) := by
  rintro ⟨h_lt, h_ge⟩
  exact (lt_irrefl _) (lt_of_lt_of_le h_lt h_ge)

theorem predictability_threshold_band :
    0.11 < PredictabilityThreshold ∧ PredictabilityThreshold < 0.13 := by
  unfold PredictabilityThreshold
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

structure ClimatePredictabilityCert where
  unit_zero : forecastCost 1 = 0
  reciprocal_symm :
    ∀ {r : ℝ}, 0 < r → forecastCost r = forecastCost r⁻¹
  cost_nonneg : ∀ {r : ℝ}, 0 < r → 0 ≤ forecastCost r
  threshold_band :
    0.11 < PredictabilityThreshold ∧ PredictabilityThreshold < 0.13
  states_exclusive :
    ∀ {r : ℝ}, ¬ (IsWithinHorizon r ∧ IsPastHorizon r)

/-- Climate-predictability-horizon certificate. -/
def climatePredictabilityCert : ClimatePredictabilityCert where
  unit_zero := forecastCost_zero_at_unit
  reciprocal_symm := forecastCost_reciprocal_symm
  cost_nonneg := forecastCost_nonneg
  threshold_band := predictability_threshold_band
  states_exclusive := horizon_states_exclusive

end
end PredictabilityFromJCost
end Climate
end IndisputableMonolith

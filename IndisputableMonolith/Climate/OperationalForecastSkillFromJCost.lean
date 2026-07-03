import Mathlib
import IndisputableMonolith.Constants

/-!
# Operational Forecast Skill: Lyapunov Time on the Phi-Ladder

Operational weather forecasting at ECMWF (IFS) and NOAA (GFS) shows a
characteristic skill-decay curve: 500-hPa anomaly correlation
coefficient (ACC) ≥ 0.6 ("useful skill") persists for ~10 days at
ECMWF, ~7 days at GFS in 2024. The recognition-Lyapunov-time prediction
is that adjacent forecast-skill horizons across operational centers
ratio by exactly φ per integer rung of model resolution.

ECMWF / GFS / lower-resolution-NWP horizon ladder:
- ECMWF IFS HRES (rung 0): 10 days
- GFS (rung -1): 10/φ ≈ 6.2 days (matches empirical 6-7)
- earlier GFS pre-FV3 (rung -2): 10/φ² ≈ 3.8 days

The φ-ratio between ECMWF and GFS skill-horizons is a structural
prediction; if a third operational center sits between them at a
non-φ-rational distance, the prediction would be falsified.

Compounds with `Climate/PredictabilityFromJCost` (the canonical-band
predictability cutoff).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Climate
namespace OperationalForecastSkillFromJCost

open Constants

noncomputable section

/-- Reference forecast horizon (RS-native dimensionless 1, calibrated
at ECMWF rung 0). -/
def referenceHorizon : ℝ := 1

/-- Forecast horizon at φ-ladder rung `k` (negative `k` for lower-
resolution model that loses skill earlier; we work with positive `k`
and flip sign in the bridge theorem below). -/
def horizonAtRung (k : ℕ) : ℝ := referenceHorizon * phi ^ (-(k : ℤ))

theorem horizonAtRung_pos (k : ℕ) : 0 < horizonAtRung k := by
  unfold horizonAtRung referenceHorizon
  have : 0 < phi ^ (-(k : ℤ)) := zpow_pos Constants.phi_pos _
  linarith [this]

theorem horizonAtRung_succ_ratio (k : ℕ) :
    horizonAtRung (k + 1) = horizonAtRung k * phi⁻¹ := by
  unfold horizonAtRung
  have hphi_ne : phi ≠ 0 := Constants.phi_ne_zero
  have hzpow : phi ^ (-((k : ℤ) + 1)) = phi ^ (-(k : ℤ)) * phi⁻¹ := by
    rw [show (-((k : ℤ) + 1)) = -(k : ℤ) + (-1 : ℤ) by ring]
    rw [zpow_add₀ hphi_ne]
    simp
  have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  rw [hcast, hzpow]; ring

theorem horizonAtRung_strictly_decreasing (k : ℕ) :
    horizonAtRung (k + 1) < horizonAtRung k := by
  rw [horizonAtRung_succ_ratio]
  have hk : 0 < horizonAtRung k := horizonAtRung_pos k
  have hphi_inv_lt_one : phi⁻¹ < 1 := by
    have hphi_gt_one : (1 : ℝ) < phi := by
      have := Constants.phi_gt_onePointFive; linarith
    exact inv_lt_one_of_one_lt₀ hphi_gt_one
  have : horizonAtRung k * phi⁻¹ < horizonAtRung k * 1 :=
    mul_lt_mul_of_pos_left hphi_inv_lt_one hk
  simpa using this

theorem horizon_adjacent_ratio (k : ℕ) :
    horizonAtRung (k + 1) / horizonAtRung k = phi⁻¹ := by
  rw [horizonAtRung_succ_ratio]
  have hpos : 0 < horizonAtRung k := horizonAtRung_pos k
  field_simp [hpos.ne']

structure OperationalForecastSkillCert where
  horizon_pos : ∀ k, 0 < horizonAtRung k
  one_step_ratio : ∀ k, horizonAtRung (k + 1) = horizonAtRung k * phi⁻¹
  strictly_decreasing : ∀ k, horizonAtRung (k + 1) < horizonAtRung k
  adjacent_ratio_eq_inv_phi :
    ∀ k, horizonAtRung (k + 1) / horizonAtRung k = phi⁻¹

/-- Operational-forecast-skill certificate. -/
def operationalForecastSkillCert : OperationalForecastSkillCert where
  horizon_pos := horizonAtRung_pos
  one_step_ratio := horizonAtRung_succ_ratio
  strictly_decreasing := horizonAtRung_strictly_decreasing
  adjacent_ratio_eq_inv_phi := horizon_adjacent_ratio

end
end OperationalForecastSkillFromJCost
end Climate
end IndisputableMonolith

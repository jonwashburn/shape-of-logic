import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core
import IndisputableMonolith.Verification.Preregistered.Hubble.Prediction
import IndisputableMonolith.Verification.Preregistered.Hubble.Measurement_2022
import IndisputableMonolith.Physics.CKMGeometry
import IndisputableMonolith.Constants.Alpha

/-!
# Tests: Hubble ratio (relative error) and Ω_Λ (within 1σ)
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace Hubble

open Preregistered
open IndisputableMonolith.Constants

/-- Hubble test: RS ratio predicts late from early within 0.05% relative error. -/
theorem hubble_ratio_passes_rel_0p05pct :
    abs (H_early * hubble_ratio.val - H_late) / H_late < 0.0005 := by
  -- Pure arithmetic check with the measurement module’s numbers.
  simp [H_early, H_late, hubble_ratio]
  norm_num

/-! Ω_Λ test needs a small bound on α/π, derived from existing α bounds. -/

theorem alpha_over_pi_bounds :
    (0.0023 : ℝ) < alpha / Real.pi ∧ alpha / Real.pi < (0.0024 : ℝ) := by
  have h_alpha_lower := Physics.CKMGeometry.alpha_lower_bound
  have h_alpha_upper := Physics.CKMGeometry.alpha_upper_bound
  have h_pi_lower : (3.14 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have h_pi_upper : Real.pi < (3.15 : ℝ) := by linarith [Real.pi_lt_d6]
  have h_alpha_pos : 0 < alpha := lt_trans (by norm_num) h_alpha_lower
  have h_pi_pos : 0 < Real.pi := Real.pi_pos
  constructor
  · -- Lower bound: 0.0023 < alpha/pi
    calc (0.0023 : ℝ) < 0.00729 / 3.15 := by norm_num
      _ < alpha / 3.15 := by
          apply div_lt_div_of_pos_right h_alpha_lower
          norm_num
      _ < alpha / Real.pi := by
          apply div_lt_div_of_pos_left h_alpha_pos h_pi_pos
          exact h_pi_upper
  · -- Upper bound: alpha/pi < 0.0024
    calc alpha / Real.pi < alpha / 3.14 := by
          apply div_lt_div_of_pos_left h_alpha_pos (by norm_num) h_pi_lower
      _ < 0.00731 / 3.14 := by
          apply div_lt_div_of_pos_right h_alpha_upper
          norm_num
      _ < (0.0024 : ℝ) := by norm_num

theorem omega_lambda_passes_1sigma :
    within_sigma omega_lambda omega_lambda_measurement := by
  unfold Preregistered.within_sigma
  -- Expand only the measurement payload; keep `alpha` opaque (do NOT simp-unfold it).
  simp [omega_lambda_measurement]
  -- Freeze the prediction formula in a stable, human-readable form:
  change |((11 : ℝ) / 16 - alpha / Real.pi) - 0.6847| < (0.0073 : ℝ)
  have h_ap := alpha_over_pi_bounds
  -- `omega_lambda.val = 0.6875 - alpha/pi` and alpha/pi ∈ (0.0023, 0.0024)
  have h_pred_lower : (0.6851 : ℝ) < (11 : ℝ) / 16 - alpha / Real.pi := by
    have h2 : (11 : ℝ) / 16 = (0.6875 : ℝ) := by norm_num
    linarith [h_ap.2, h2]
  have h_pred_upper : (11 : ℝ) / 16 - alpha / Real.pi < (0.6852 : ℝ) := by
    have h2 : (11 : ℝ) / 16 = (0.6875 : ℝ) := by norm_num
    linarith [h_ap.1, h2]
  -- Since pred > 0.6851 > 0.6847, the difference is positive, so `abs` drops.
  have hpos : (0 : ℝ) < ((11 : ℝ) / 16 - alpha / Real.pi) - 0.6847 := by
    have : (0.6851 : ℝ) < (11 : ℝ) / 16 - alpha / Real.pi := h_pred_lower
    linarith
  have habs :
      |((11 : ℝ) / 16 - alpha / Real.pi) - 0.6847| =
        ((11 : ℝ) / 16 - alpha / Real.pi) - 0.6847 :=
    abs_of_pos hpos
  rw [habs]
  have hsmall : ((11 : ℝ) / 16 - alpha / Real.pi) - 0.6847 < (0.0073 : ℝ) := by
    have : (11 : ℝ) / 16 - alpha / Real.pi < (0.6852 : ℝ) := h_pred_upper
    linarith
  exact hsmall

end Hubble
end Preregistered
end Verification
end IndisputableMonolith

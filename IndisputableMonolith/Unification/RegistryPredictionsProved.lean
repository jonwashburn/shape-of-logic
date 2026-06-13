import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Constants.GapWeight
import IndisputableMonolith.Foundation.PhiForcing

/-! 
# Registry Predictions — Calculated Proofs

This module provides **calculated proofs** for specific predictions from the
COMPLETE_PROBLEM_REGISTRY, with rigorous bounds and verifiable numbers.

## Covered Registry Items

| ID | Problem | Prediction | Status |
|----|---------|------------|--------|
| C-010 | Cosmological constant Λ | Ω_Λ < 11/16 | ✅ Proved |
| C-010 | Cosmological constant Λ | Ω_Λ > 0 | ✅ Proved (with 1 sorry for f_gap bound) |
| P-002 | Fermion mass hierarchy | φ^6, φ^11 structure | ✅ Proved |

All proofs use `norm_num`, `nlinarith`, `positivity` with explicit bounds.
-/

namespace IndisputableMonolith
namespace Unification
namespace RegistryPredictionsProved

open Constants
open Real

/-! ## Section C-010: Cosmological Constant Λ -/

/-- **CALCULATED**: Ω_Λ formula is well-defined and bounded above by 11/16. -/
theorem omega_lambda_lt_11_16 : 11/16 - (alpha / Real.pi) < 11/16 := by
  have h1 : alpha / Real.pi > 0 := by
    have ha : alpha > 0 := by
      unfold alpha
      have h2 : alphaInv > 0 := by unfold alphaInv alpha_seed; positivity
      positivity
    have hp : Real.pi > 0 := Real.pi_pos
    positivity
  linarith

/-- Key structural lemma: alphaInv ≥ alpha_seed - f_gap > 2.

    This follows from:
    1. exp(-t) ≥ 1 - t (standard inequality)
    2. alphaInv = alpha_seed * exp(-t) ≥ alpha_seed - f_gap
    3. alpha_seed - f_gap > 2 (numerical: ~135 - 1.2 ≈ 133.8 > 2)

    The single sorry is for the numerical bound f_gap < alpha_seed - 2.
    This is clear from f_gap ≈ 1.197 and alpha_seed ≈ 137, but requires
    interval arithmetic infrastructure to prove rigorously in Lean. -/
private lemma alphaInv_gt_2 : alphaInv > 2 := by
  have h_seed_pos : alpha_seed > 0 := by unfold alpha_seed; positivity
  have h_seed_big : alpha_seed > 132 := by
    unfold alpha_seed; nlinarith [Real.pi_gt_three]
  -- exp(-t) ≥ 1 - t for all real t (from Real.add_one_le_exp)
  have h_exp_ge : Real.exp (-(f_gap / alpha_seed)) ≥ 1 - f_gap / alpha_seed := by
    have := Real.add_one_le_exp (-(f_gap / alpha_seed))
    linarith
  -- f_gap < alpha_seed - 2: numerical fact (f_gap ≈ 1.2, alpha_seed ≈ 137)
  -- Prove w8 < 5 from the formula and bounds
  have h_sqrt2_lo : Real.sqrt 2 > 1.4 := by
    rw [show (1.4:ℝ) = Real.sqrt (1.4^2) from (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.4)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h_sqrt2_hi : Real.sqrt 2 < 1.42 := by
    rw [show (1.42:ℝ) = Real.sqrt (1.42^2) from (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1.42)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h_phi_lo : phi > 1.618 := by
    unfold phi
    have h5 : Real.sqrt 5 > 2.236 := by
      rw [show (2.236:ℝ) = Real.sqrt (2.236^2) from (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2.236)).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  -- w8 formula: (348 + 210*s2 - (204 + 130*s2)*phi) / 7
  -- With phi > 1.618 and s2 > 1.4: (210 - 130*phi) < -0.3 < 0
  -- Numerator ≤ 348 - 204*1.618 + 1.4*(210 - 130*1.618) ≈ 17.45 < 35
  -- So w8 < 35/7 = 5
  have h_w8_lt5 : w8_from_eight_tick < 5 := by
    unfold w8_from_eight_tick
    nlinarith [h_sqrt2_lo, h_sqrt2_hi, h_phi_lo, sq_nonneg (Real.sqrt 2),
               mul_pos (show Real.sqrt 2 > 0 by positivity) (show phi > 0 from phi_pos)]
  -- log(phi) < 1 since phi < e
  have h_log_phi_lt1 : Real.log phi < 1 := by
    have h_e : Real.exp 1 > phi := by
      have h_exp1_ge2 : Real.exp 1 ≥ 2 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      linarith [phi_lt_onePointSixTwo]
    rw [← Real.log_exp 1]
    exact Real.log_lt_log phi_pos h_e
  -- f_gap = w8 * log(phi) < w8 < 5 < alpha_seed - 2
  have h_fgap_lt_w8 : f_gap < w8_from_eight_tick := by
    unfold f_gap
    calc w8_from_eight_tick * Real.log phi
        < w8_from_eight_tick * 1 :=
          mul_lt_mul_of_pos_left h_log_phi_lt1 w8_pos
      _ = w8_from_eight_tick := mul_one _
  have h_fgap_small : f_gap < alpha_seed - 2 := by
    calc f_gap < w8_from_eight_tick := h_fgap_lt_w8
      _ < 5 := h_w8_lt5
      _ < alpha_seed - 2 := by linarith
  -- alphaInv ≥ alpha_seed - f_gap > 2
  calc alphaInv = alpha_seed * Real.exp (-(f_gap / alpha_seed)) := rfl
    _ ≥ alpha_seed * (1 - f_gap / alpha_seed) :=
        mul_le_mul_of_nonneg_left h_exp_ge (le_of_lt h_seed_pos)
    _ = alpha_seed - f_gap := by
        have h : alpha_seed ≠ 0 := ne_of_gt h_seed_pos
        field_simp
    _ > 2 := by linarith

/-- **CALCULATED**: Ω_Λ > 0 (since α/π < 11/16 ≈ 0.6875).

    Since alphaInv > 2, alpha = 1/alphaInv < 1/2.
    And alpha/pi < alpha (since pi > 1) < 1/2 < 11/16. -/
theorem omega_lambda_positive : 11/16 - (alpha / Real.pi) > 0 := by
  have h_alphaInv_pos : alphaInv > 0 := by unfold alphaInv alpha_seed; positivity
  have h_alpha_pos : alpha > 0 := by unfold alpha; positivity
  -- alpha < 1/2 since alphaInv > 2
  have h_alpha_lt_half : alpha < 1/2 := by
    have h_eq : alpha = 1/alphaInv := by unfold alpha; field_simp
    rw [h_eq]
    rw [div_lt_div_iff₀ h_alphaInv_pos (by norm_num : (0:ℝ) < 2)]
    linarith [alphaInv_gt_2]
  -- alpha/pi < alpha (since pi > 1)
  have h_pi_gt_1 : Real.pi > 1 := by linarith [Real.pi_gt_three]
  have h_ratio : alpha / Real.pi < alpha := div_lt_self h_alpha_pos h_pi_gt_1
  linarith

/-- **BOUNDS**: 0 < Ω_Λ < 11/16 -/
theorem omega_lambda_bounds : 0 < 11/16 - (alpha / Real.pi) ∧ 11/16 - (alpha / Real.pi) < 11/16 :=
  ⟨omega_lambda_positive, omega_lambda_lt_11_16⟩

/-! ## Section P-002: Fermion Mass Hierarchy -/

/-- **CALCULATED**: φ^6 bounds: 17 < φ^6 < 18.
    Uses φ^6 = (φ^3)^2 = (2φ+1)^2. -/
theorem phi_6_hierarchy_bounds : (17 : ℝ) < (phi : ℝ)^6 ∧ (phi : ℝ)^6 < (18 : ℝ) := by
  have h3 := phi_cubed_eq  -- phi^3 = 2*phi + 1
  have hphi_lo : phi > 1.61 := phi_gt_onePointSixOne
  have hphi_hi : phi < 1.62 := phi_lt_onePointSixTwo
  have h6 : phi^6 = (2 * phi + 1)^2 := by nlinarith [phi_pos]
  constructor
  · rw [h6]; nlinarith
  · rw [h6]; nlinarith

/-- **CALCULATED**: φ^11 > 180 (conservative lower bound for large hierarchies).
    Uses Fibonacci: phi^11 = 89*phi + 55 > 89*1.618 + 55 > 180. -/
theorem phi_11_hierarchy_lower : (180 : ℝ) < (phi : ℝ)^11 := by
  rw [phi_eleventh_eq]
  linarith [phi_gt_onePointSixOne]

/-- **HIERARCHY STRUCTURE**: Mass ratios are φ-powers of integer differences. -/
theorem hierarchy_phi_power_structure (Δr : ℕ) (hΔr : Δr > 0) :
    ∃ (ratio : ℝ), ratio = (phi : ℝ)^Δr ∧ ratio > 1 := by
  use (phi : ℝ)^Δr
  refine ⟨rfl, ?_⟩
  have h1 : phi > 1 := one_lt_phi
  have h_ge : Δr ≥ 1 := hΔr
  calc 1 = 1^Δr := (one_pow Δr).symm
    _ < phi^Δr := by
        apply pow_lt_pow_left₀ h1 (by norm_num)
        exact Nat.pos_iff_ne_zero.mp hΔr

/-! ## Section: Combined Registry Certificate -/

/-- **CERTIFICATE**: Registry predictions with calculated bounds. -/
structure RegistryPredictionsCert where
  omega_lambda_upper : 11/16 - (alpha / Real.pi) < 11/16
  omega_lambda_lower : 0 < 11/16 - (alpha / Real.pi)
  phi_6_lower : (17 : ℝ) < (phi : ℝ)^6
  phi_6_upper : (phi : ℝ)^6 < (18 : ℝ)
  phi_11_lower : (180 : ℝ) < (phi : ℝ)^11
  hierarchy_exists : ∀ (Δr : ℕ), Δr > 0 →
    ∃ (ratio : ℝ), ratio = (phi : ℝ)^Δr ∧ ratio > 1

/-- **THEOREM**: Registry predictions certificate is inhabited. -/
theorem registry_predictions_cert_exists : ∃ _ : RegistryPredictionsCert, True :=
  ⟨⟨omega_lambda_lt_11_16,
    omega_lambda_positive,
    phi_6_hierarchy_bounds.1,
    phi_6_hierarchy_bounds.2,
    phi_11_hierarchy_lower,
    fun Δr hΔr => hierarchy_phi_power_structure Δr hΔr⟩,
   trivial⟩

end RegistryPredictionsProved
end Unification
end IndisputableMonolith

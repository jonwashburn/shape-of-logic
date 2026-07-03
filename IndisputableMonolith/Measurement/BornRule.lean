import Mathlib
import IndisputableMonolith.Measurement.PathAction
import IndisputableMonolith.Measurement.C2ABridge

/-!
# Born Rule from Recognition Cost

This module derives Born's rule P(I) = |α_I|² from the recognition
cost functional J and the amplitude bridge 𝒜 = exp(-C/2)·exp(iφ).
-/

namespace IndisputableMonolith
namespace Measurement

open Real Complex

/-- Two-outcome measurement probabilities from recognition weights -/
structure TwoOutcomeMeasurement where
  C₁ : ℝ  -- Recognition cost for outcome 1
  C₂ : ℝ  -- Recognition cost for outcome 2
  C₁_nonneg : 0 ≤ C₁
  C₂_nonneg : 0 ≤ C₂

/-- Probability of outcome 1 -/
noncomputable def prob₁ (m : TwoOutcomeMeasurement) : ℝ :=
  Real.exp (-m.C₁) / (Real.exp (-m.C₁) + Real.exp (-m.C₂))

/-- Probability of outcome 2 -/
noncomputable def prob₂ (m : TwoOutcomeMeasurement) : ℝ :=
  Real.exp (-m.C₂) / (Real.exp (-m.C₁) + Real.exp (-m.C₂))

/-- Probabilities are non-negative -/
lemma prob₁_nonneg (m : TwoOutcomeMeasurement) : 0 ≤ prob₁ m := by
  unfold prob₁
  apply div_nonneg
  · exact (Real.exp_pos _).le
  · exact (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

lemma prob₂_nonneg (m : TwoOutcomeMeasurement) : 0 ≤ prob₂ m := by
  unfold prob₂
  apply div_nonneg
  · exact (Real.exp_pos _).le
  · exact (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

/-- Probabilities sum to 1 (normalization) -/
theorem probabilities_normalized (m : TwoOutcomeMeasurement) :
  prob₁ m + prob₂ m = 1 := by
  unfold prob₁ prob₂
  have hdenom : Real.exp (-m.C₁) + Real.exp (-m.C₂) ≠ 0 :=
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  set denom : ℝ := Real.exp (-m.C₁) + Real.exp (-m.C₂)
  have hadd :
      Real.exp (-m.C₁) / denom + Real.exp (-m.C₂) / denom = (Real.exp (-m.C₁) + Real.exp (-m.C₂)) / denom := by
    simpa [denom] using (add_div (Real.exp (-m.C₁)) (Real.exp (-m.C₂)) denom).symm
  -- Finish.
  simpa [denom, hadd] using (div_self hdenom)

/-- Born rule: probabilities match quantum amplitude squares -/
theorem born_rule_from_C (α₁ α₂ : ℂ)
  (_hα : ‖α₁‖ ^ 2 + ‖α₂‖ ^ 2 = 1)
  (rot : TwoBranchRotation)
  (hrot₁ : ‖α₁‖ ^ 2 = complementAmplitudeSquared rot)
  (hrot₂ : ‖α₂‖ ^ 2 = initialAmplitudeSquared rot) :
  ∃ m : TwoOutcomeMeasurement,
    prob₁ m = ‖α₁‖ ^ 2 ∧
    prob₂ m = ‖α₂‖ ^ 2 := by
  -- Construct the measurement from the rate action
  -- From C_equals_2A, we have C = 2A where A = -ln(sin θ_s)
  -- So exp(-C) = exp(-2A) = sin²(θ_s) = |α₂|²

  -- We use two costs:
  --   * `C_sin`: the RS path action cost (so exp(-C_sin) = sin² θ by the bridge),
  --   * `C_cos`: the complementary cost -2 log(cos θ) (so exp(-C_cos) = cos² θ).
  let C_sin := pathAction (pathFromRotation rot)
  let C_cos := -2 * Real.log (Real.cos rot.θ_s)

  have hCsin_nonneg : 0 ≤ C_sin := by
    unfold C_sin pathAction
    -- pathAction is an integral of Jcost over positive rates
    -- Jcost(r) ≥ 0 for all r > 0 (proven in Cost module)
    refine intervalIntegral.integral_nonneg ?_ ?_
    · exact le_of_lt (pathFromRotation rot).T_pos
    · intro t ht
      apply Cost.Jcost_nonneg
      exact (pathFromRotation rot).rate_pos t ht

  have hCcos_nonneg : 0 ≤ C_cos := by
    unfold C_cos
    have hneg2 : (-2 : ℝ) ≤ 0 := by norm_num
    have hlog : Real.log (Real.cos rot.θ_s) ≤ 0 := by
      apply Real.log_nonpos
      ·
        have hpi2 : (0 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_pos]
        have hneg : (-(Real.pi / 2) : ℝ) < rot.θ_s := lt_trans (neg_lt_zero.mpr hpi2) rot.θ_s_bounds.1
        exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨hneg, rot.θ_s_bounds.2⟩)
      · exact Real.cos_le_one _
    exact mul_nonneg_of_nonpos_of_nonpos hneg2 hlog

  let m : TwoOutcomeMeasurement := {
    -- Convention: outcome 1 is the cos-branch (complement), outcome 2 is the sin-branch (initial).
    C₁ := C_cos
    C₂ := C_sin
    C₁_nonneg := hCcos_nonneg
    C₂_nonneg := hCsin_nonneg
  }

  use m
  constructor
  · -- prob₁ m = ‖α₁‖²
    unfold prob₁
    -- Reduce to cos² / (cos² + sin²) = cos².
    rw [hrot₁]
    have hcos : Real.exp (-C_cos) = complementAmplitudeSquared rot := by
      -- exp(-(-2 log cos)) = cos²
      have hcos_pos : 0 < Real.cos rot.θ_s := by
        refine Real.cos_pos_of_mem_Ioo ?_
        refine ⟨?_, rot.θ_s_bounds.2⟩
        have hpi2 : (0 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_pos]
        linarith [rot.θ_s_bounds.1, hpi2]
      unfold C_cos complementAmplitudeSquared
      calc
        Real.exp (-(-2 * Real.log (Real.cos rot.θ_s)))
            = Real.exp (2 * Real.log (Real.cos rot.θ_s)) := by ring_nf
        _ = Real.exp (Real.log ((Real.cos rot.θ_s) ^ 2)) := by
            congr 1
            exact (Real.log_pow (Real.cos rot.θ_s) 2).symm
        _ = (Real.cos rot.θ_s) ^ 2 := Real.exp_log (pow_pos hcos_pos 2)
    have hsin : Real.exp (-C_sin) = initialAmplitudeSquared rot := by
      -- exp(-pathAction) = pathWeight = sin²
      have h := weight_equals_born rot
      simpa [pathWeight, C_sin] using h
    rw [hcos, hsin]
    simp [complementAmplitudeSquared, initialAmplitudeSquared, Real.cos_sq_add_sin_sq rot.θ_s]
  · -- prob₂ m = ‖α₂‖²
    unfold prob₂
    rw [hrot₂]
    -- Reduce to sin² / (cos² + sin²) = sin².
    have hcos : Real.exp (-C_cos) = complementAmplitudeSquared rot := by
      have hcos_pos : 0 < Real.cos rot.θ_s := by
        refine Real.cos_pos_of_mem_Ioo ?_
        refine ⟨?_, rot.θ_s_bounds.2⟩
        have hpi2 : (0 : ℝ) < Real.pi / 2 := by nlinarith [Real.pi_pos]
        linarith [rot.θ_s_bounds.1, hpi2]
      unfold C_cos complementAmplitudeSquared
      calc
        Real.exp (-(-2 * Real.log (Real.cos rot.θ_s)))
            = Real.exp (2 * Real.log (Real.cos rot.θ_s)) := by ring_nf
        _ = Real.exp (Real.log ((Real.cos rot.θ_s) ^ 2)) := by
            congr 1
            exact (Real.log_pow (Real.cos rot.θ_s) 2).symm
        _ = (Real.cos rot.θ_s) ^ 2 := Real.exp_log (pow_pos hcos_pos 2)
    have hsin : Real.exp (-C_sin) = initialAmplitudeSquared rot := by
      have h := weight_equals_born rot
      simpa [pathWeight, C_sin] using h
    -- The definition of `prob₂` uses exp(-C₂), and `m.C₂ = C_sin`.
    -- So we rewrite and conclude.
    -- (Note: `unfold` above expanded `C₁`/`C₂` fields of `m` to the right constants.)
    rw [hcos, hsin]
    simp [complementAmplitudeSquared, initialAmplitudeSquared, Real.cos_sq_add_sin_sq rot.θ_s]

/-- Born rule normalized: from recognition costs to normalized probabilities -/
theorem born_rule_normalized (C₁ C₂ : ℝ) (α₁ α₂ : ℂ)
  (h₁ : Real.exp (-C₁) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₁‖ ^ 2)
  (h₂ : Real.exp (-C₂) / (Real.exp (-C₁) + Real.exp (-C₂)) = ‖α₂‖ ^ 2) :
  ‖α₁‖ ^ 2 + ‖α₂‖ ^ 2 = 1 := by
  have hdenom : Real.exp (-C₁) + Real.exp (-C₂) ≠ 0 :=
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  calc ‖α₁‖ ^ 2 + ‖α₂‖ ^ 2
      = Real.exp (-C₁) / (Real.exp (-C₁) + Real.exp (-C₂)) +
        Real.exp (-C₂) / (Real.exp (-C₁) + Real.exp (-C₂)) := by rw [← h₁, ← h₂]
      _ = (Real.exp (-C₁) + Real.exp (-C₂)) / (Real.exp (-C₁) + Real.exp (-C₂)) := by
        simpa using
          (add_div (Real.exp (-C₁)) (Real.exp (-C₂)) (Real.exp (-C₁) + Real.exp (-C₂))).symm
      _ = 1 := div_self hdenom

end Measurement
end IndisputableMonolith

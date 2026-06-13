-- import IndisputableMonolith.Numerics.Interval.Basic  -- [not in public release]
-- import IndisputableMonolith.Numerics.Interval.PiBounds  -- [not in public release]
-- import IndisputableMonolith.Numerics.Interval.PhiBounds  -- [not in public release]
import IndisputableMonolith.Constants.GapWeight

namespace IndisputableMonolith.Numerics
namespace W8Bounds

open Interval
open IndisputableMonolith.Constants

/-!
## W8 Numerical Bounds

The gap weight `w8_from_eight_tick` is approximately 2.490569.

In the Lean codebase, `w8_from_eight_tick` is defined as a parameter‑free
closed form:

`w8 = (348 + 210√2 - (204 + 130√2)φ)/7`.

These theorems provide rigorous bounds using tight intervals for `φ` and `√2`.
-/

/-- Lower decimal bound for √2. -/
theorem sqrt2_gt_14142 : (1.4142 : ℝ) < Real.sqrt 2 := by
  have hx : (0 : ℝ) ≤ (1.4142 : ℝ) := by norm_num
  have hsq : (1.4142 : ℝ) ^ 2 < (2 : ℝ) := by norm_num
  exact (Real.lt_sqrt hx).2 hsq

/-- Upper decimal bound for √2. -/
theorem sqrt2_lt_14143 : Real.sqrt 2 < (1.4143 : ℝ) := by
  have hx : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hy : (0 : ℝ) ≤ (1.4143 : ℝ) := by norm_num
  have hsq : (2 : ℝ) < (1.4143 : ℝ) ^ 2 := by norm_num
  exact (Real.sqrt_lt hx hy).2 hsq

/-- Lower decimal bound for φ. -/
theorem phi_gt_161803395 : (1.61803395 : ℝ) < IndisputableMonolith.Constants.phi := by
  have hx : (0 : ℝ) ≤ (2.2360679 : ℝ) := by norm_num
  have hsq : (2.2360679 : ℝ) ^ 2 < (5 : ℝ) := by norm_num
  have hsqrt : (2.2360679 : ℝ) < Real.sqrt 5 := by
    exact (Real.lt_sqrt hx).2 hsq
  unfold IndisputableMonolith.Constants.phi
  linarith

/-- Upper decimal bound for φ. -/
theorem phi_lt_16180340 : IndisputableMonolith.Constants.phi < (1.6180340 : ℝ) := by
  have hx : (0 : ℝ) ≤ (5 : ℝ) := by norm_num
  have hy : (0 : ℝ) ≤ (2.236068 : ℝ) := by norm_num
  have hsq : (5 : ℝ) < (2.236068 : ℝ) ^ 2 := by norm_num
  have hsqrt : Real.sqrt 5 < (2.236068 : ℝ) := by
    exact (Real.sqrt_lt hx hy).2 hsq
  unfold IndisputableMonolith.Constants.phi
  linarith

/-- The gap weight is greater than 2.490564399. -/
theorem w8_computed_gt : (2.490564399 : ℝ) < IndisputableMonolith.Constants.w8_from_eight_tick := by
  -- w8 = (348 + 210√2 - (204 + 130√2)φ)/7
  have hs2_hi : Real.sqrt 2 ≤ (1.4143 : ℝ) := le_of_lt sqrt2_lt_14143
  have hφ_hi : IndisputableMonolith.Constants.phi < (1.6180340 : ℝ) := phi_lt_16180340

  -- Step 1: replace φ by its upper bound (expression decreases as φ increases).
  have h_phi_step :
      (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.6180340 : ℝ)) / 7
        ≤ (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi) / 7 := by
    have hA : 0 ≤ (204 : ℝ) + 130 * Real.sqrt 2 := by
      have : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    have hmul :
        -((204 : ℝ) + 130 * Real.sqrt 2) * (1.6180340 : ℝ)
          ≤ -((204 : ℝ) + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi := by
      have hnegA : -((204 : ℝ) + 130 * Real.sqrt 2) ≤ 0 := by linarith
      -- phi ≤ 1.6180340 and the coefficient is nonpositive, so inequality flips.
      exact mul_le_mul_of_nonpos_left hφ_hi.le hnegA
    have h7 : (0 : ℝ) < (7 : ℝ) := by norm_num
    have hnum :
        (348 : ℝ) + 210 * Real.sqrt 2 - ((204 : ℝ) + 130 * Real.sqrt 2) * (1.6180340 : ℝ)
          ≤ (348 : ℝ) + 210 * Real.sqrt 2 - ((204 : ℝ) + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi := by
      linarith [hmul]
    exact (div_le_div_of_nonneg_right hnum (le_of_lt h7))

  -- Step 2: with φ fixed at its max, the expression decreases in √2 because (210 - 130φ) < 0.
  have hcoeff_neg : (210 : ℝ) - 130 * (1.6180340 : ℝ) < 0 := by norm_num
  have h_s2_step :
      (348 + 210 * (1.4143 : ℝ) - (204 + 130 * (1.4143 : ℝ)) * (1.6180340 : ℝ)) / 7
        ≤ (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.6180340 : ℝ)) / 7 := by
    have h7 : (0 : ℝ) < (7 : ℝ) := by norm_num
    -- Rewrite numerator as `A + √2 * B` where `B < 0`, so replacing √2 by its upper bound
    -- gives a *lower* value (hence a lower corner bound).
    set B : ℝ := (210 : ℝ) - 130 * (1.6180340 : ℝ)
    have hB : B ≤ 0 := by
      have : B < 0 := by simpa [B] using hcoeff_neg
      exact le_of_lt this
    have hs2_term : (1.4143 : ℝ) * B ≤ Real.sqrt 2 * B := by
      have hs : Real.sqrt 2 ≤ (1.4143 : ℝ) := hs2_hi
      exact mul_le_mul_of_nonpos_right hs hB
    have hnum_raw :
        (348 : ℝ) - 204 * (1.6180340 : ℝ) + (1.4143 : ℝ) * B
          ≤ (348 : ℝ) - 204 * (1.6180340 : ℝ) + Real.sqrt 2 * B := by
      linarith [hs2_term]
    have hrewL :
        (348 : ℝ) - 204 * (1.6180340 : ℝ) + (1.4143 : ℝ) * B
          = (348 + 210 * (1.4143 : ℝ) - (204 + 130 * (1.4143 : ℝ)) * (1.6180340 : ℝ)) := by
      simp [B]
      ring
    have hrewR :
        (348 : ℝ) - 204 * (1.6180340 : ℝ) + Real.sqrt 2 * B
          = (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.6180340 : ℝ)) := by
      simp [B]
      ring
    have hnum' :
        (348 + 210 * (1.4143 : ℝ) - (204 + 130 * (1.4143 : ℝ)) * (1.6180340 : ℝ))
          ≤ (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.6180340 : ℝ)) := by
      simpa [hrewL, hrewR] using hnum_raw
    exact (div_le_div_of_nonneg_right hnum' (le_of_lt h7))

  -- Combine the steps.
  have hw8_corner :
      (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi) / 7
        ≥ (348 + 210 * (1.4143 : ℝ) - (204 + 130 * (1.4143 : ℝ)) * (1.6180340 : ℝ)) / 7 :=
    -- corner ≤ (φ_hi,sqrt2) ≤ (φ,sqrt2)
    show (348 + 210 * (1.4143 : ℝ) - (204 + 130 * (1.4143 : ℝ)) * (1.6180340 : ℝ)) / 7
          ≤ (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi) / 7 from
      le_trans h_s2_step h_phi_step

  -- Now the numeric corner value is > 2.490564399.
  have hcorner_gt :
      (2.490564399 : ℝ) <
        (348 + 210 * (1.4143 : ℝ) - (204 + 130 * (1.4143 : ℝ)) * (1.6180340 : ℝ)) / 7 := by
    norm_num

  -- Finish by unfolding w8 and chaining inequalities.
  unfold IndisputableMonolith.Constants.w8_from_eight_tick
  exact lt_of_lt_of_le hcorner_gt hw8_corner

/-- The gap weight is less than 2.490572090. -/
theorem w8_computed_lt : IndisputableMonolith.Constants.w8_from_eight_tick < (2.490572090 : ℝ) := by
  -- Upper bound by the “best-case corner” (√2 minimal, φ minimal).
  have hs2_lo : (1.4142 : ℝ) ≤ Real.sqrt 2 := le_of_lt sqrt2_gt_14142
  have hφ_lo : (1.61803395 : ℝ) ≤ IndisputableMonolith.Constants.phi := by
    exact le_of_lt phi_gt_161803395

  -- Step 1: replace φ by its lower bound (expression increases as φ decreases).
  have h_phi_step :
      (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi) / 7
        ≤ (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.61803395 : ℝ)) / 7 := by
    have hA : 0 ≤ (204 : ℝ) + 130 * Real.sqrt 2 := by
      have : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith
    have hmul :
        -((204 : ℝ) + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi
          ≤ -((204 : ℝ) + 130 * Real.sqrt 2) * (1.61803395 : ℝ) := by
      have hnegA : -((204 : ℝ) + 130 * Real.sqrt 2) ≤ 0 := by linarith
      exact mul_le_mul_of_nonpos_left hφ_lo hnegA
    have h7 : (0 : ℝ) < (7 : ℝ) := by norm_num
    have hnum :
        (348 : ℝ) + 210 * Real.sqrt 2 - ((204 : ℝ) + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi
          ≤ (348 : ℝ) + 210 * Real.sqrt 2 - ((204 : ℝ) + 130 * Real.sqrt 2) * (1.61803395 : ℝ) := by
      linarith [hmul]
    exact (div_le_div_of_nonneg_right hnum (le_of_lt h7))

  -- Step 2: with φ fixed at its min, the expression increases in √2 because (210 - 130φ) < 0,
  -- so taking √2 at its lower bound gives an upper bound for the whole expression.
  have hcoeff_neg : (210 : ℝ) - 130 * (1.61803395 : ℝ) < 0 := by norm_num
  have h_s2_step :
      (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.61803395 : ℝ)) / 7
        ≤ (348 + 210 * (1.4142 : ℝ) - (204 + 130 * (1.4142 : ℝ)) * (1.61803395 : ℝ)) / 7 := by
    have h7 : (0 : ℝ) < (7 : ℝ) := by norm_num
    have hs2_term :
        Real.sqrt 2 * ((210 : ℝ) - 130 * (1.61803395 : ℝ))
          ≤ (1.4142 : ℝ) * ((210 : ℝ) - 130 * (1.61803395 : ℝ)) := by
      have : (1.4142 : ℝ) ≤ Real.sqrt 2 := hs2_lo
      have hcoeff_nonpos : ((210 : ℝ) - 130 * (1.61803395 : ℝ)) ≤ 0 := le_of_lt hcoeff_neg
      exact mul_le_mul_of_nonpos_right this hcoeff_nonpos
    have hnum :
        (348 : ℝ) - 204 * (1.61803395 : ℝ) + Real.sqrt 2 * ((210 : ℝ) - 130 * (1.61803395 : ℝ))
          ≤ (348 : ℝ) - 204 * (1.61803395 : ℝ) + (1.4142 : ℝ) * ((210 : ℝ) - 130 * (1.61803395 : ℝ)) := by
      linarith
    have hrew1 :
        (348 : ℝ) - 204 * (1.61803395 : ℝ) + Real.sqrt 2 * ((210 : ℝ) - 130 * (1.61803395 : ℝ))
          = (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.61803395 : ℝ)) := by
      ring
    have hrew2 :
        (348 : ℝ) - 204 * (1.61803395 : ℝ) + (1.4142 : ℝ) * ((210 : ℝ) - 130 * (1.61803395 : ℝ))
          = (348 + 210 * (1.4142 : ℝ) - (204 + 130 * (1.4142 : ℝ)) * (1.61803395 : ℝ)) := by
      ring
    have hnum' :
        (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * (1.61803395 : ℝ))
          ≤ (348 + 210 * (1.4142 : ℝ) - (204 + 130 * (1.4142 : ℝ)) * (1.61803395 : ℝ)) := by
      simpa [hrew1, hrew2] using hnum
    exact (div_le_div_of_nonneg_right hnum' (le_of_lt h7))

  -- Combine the steps.
  have hw8_corner :
      (348 + 210 * Real.sqrt 2 - (204 + 130 * Real.sqrt 2) * IndisputableMonolith.Constants.phi) / 7
        ≤ (348 + 210 * (1.4142 : ℝ) - (204 + 130 * (1.4142 : ℝ)) * (1.61803395 : ℝ)) / 7 :=
    le_trans h_phi_step h_s2_step

  -- Now the numeric corner value is < 2.490572090.
  have hcorner_lt :
      (348 + 210 * (1.4142 : ℝ) - (204 + 130 * (1.4142 : ℝ)) * (1.61803395 : ℝ)) / 7 < (2.490572090 : ℝ) := by
    norm_num

  -- Finish by unfolding w8 and chaining inequalities.
  unfold IndisputableMonolith.Constants.w8_from_eight_tick
  exact lt_of_le_of_lt hw8_corner hcorner_lt

/-- The gap weight interval for alphaInv bounds. -/
def w8Interval : Set ℝ :=
  Set.Icc (2490564399 / 1000000000 : ℝ) (2490572090 / 1000000000 : ℝ)

end W8Bounds
end IndisputableMonolith.Numerics

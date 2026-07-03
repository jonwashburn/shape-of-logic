import IndisputableMonolith.Numerics.Interval.Basic
import IndisputableMonolith.Numerics.Interval.Exp
import IndisputableMonolith.Numerics.Interval.Log
import IndisputableMonolith.Numerics.Interval.PhiBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Interval Arithmetic for Power Function

This module provides rigorous interval bounds for the power function x^y
using the identity x^y = exp(y * log x) for x > 0.

## Strategy

For x in [lo_x, hi_x] ⊆ (0, ∞) and y in [lo_y, hi_y]:
1. Compute interval for log(x) using log monotonicity
2. Multiply by y interval
3. Apply exp to get final interval

For the special case of x^n where n is a natural number, we use
direct computation which is more precise.
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real (exp log rpow goldenRatio)

/-- Simple power interval using explicit bounds.
    Given bounds on the final result, just package them. -/
def rpowIntervalSimple
    (result_lo result_hi : ℚ)
    (h_valid : result_lo ≤ result_hi) : Interval where
  lo := result_lo
  hi := result_hi
  valid := h_valid

/-- The simple power interval contains x^y if the bounds are correct -/
theorem rpowIntervalSimple_contains_rpow
    {result_lo result_hi : ℚ}
    (h_valid : result_lo ≤ result_hi)
    {x y : ℝ}
    (h_lo : (result_lo : ℝ) ≤ x.rpow y)
    (h_hi : x.rpow y ≤ (result_hi : ℝ)) :
    (rpowIntervalSimple result_lo result_hi h_valid).contains (x.rpow y) :=
  ⟨h_lo, h_hi⟩

/-- Interval containing φ = (1 + √5)/2 ≈ 1.618 -/
def phiInterval : Interval where
  lo := 1618 / 1000
  hi := 1619 / 1000
  valid := by norm_num

/-- φ is in phiInterval - PROVEN using sqrt bounds -/
theorem phi_in_phiInterval : phiInterval.contains ((1 + Real.sqrt 5) / 2) := by
  simp only [Interval.contains, phiInterval]
  constructor
  · have h := phi_gt_1618
    have h1 : ((1618 / 1000 : ℚ) : ℝ) < (1 + Real.sqrt 5) / 2 := by
      calc ((1618 / 1000 : ℚ) : ℝ) = (1.618 : ℝ) := by norm_num
        _ < (1 + Real.sqrt 5) / 2 := h
    exact le_of_lt h1
  · have h := phi_lt_16185
    have h1 : (1 + Real.sqrt 5) / 2 < ((1619 / 1000 : ℚ) : ℝ) := by
      calc (1 + Real.sqrt 5) / 2 < (1.6185 : ℝ) := h
        _ < (1.619 : ℝ) := by norm_num
        _ = ((1619 / 1000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt h1

/-- φ = (1 + √5)/2 (Mathlib definition) -/
theorem phi_eq_formula : goldenRatio = (1 + Real.sqrt 5) / 2 := rfl

/-- φ^(-5) interval ≈ 0.0902 - PROVEN using φ⁻⁵ = (φ⁻¹)⁵ -/
def phi_pow_neg5_interval : Interval where
  lo := 89 / 1000  -- Matches phi_inv5_interval_proven
  hi := 91 / 1000
  valid := by norm_num

theorem phi_pow_neg5_in_interval : phi_pow_neg5_interval.contains (((1 + Real.sqrt 5) / 2) ^ (-5 : ℝ)) := by
  -- φ^(-5) = (φ⁻¹)^5
  simp only [Interval.contains, phi_pow_neg5_interval]
  rw [← phi_eq_formula]
  have hpos : (0 : ℝ) < goldenRatio := Real.goldenRatio_pos
  have h : goldenRatio ^ (-5 : ℝ) = goldenRatio⁻¹ ^ 5 := by
    rw [Real.rpow_neg (le_of_lt hpos)]
    have : (5 : ℝ) = (5 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast, inv_pow]
  rw [h]
  have hcontains := phi_inv5_in_interval_proven
  simp only [Interval.contains, phi_inv5_interval_proven] at hcontains
  constructor
  · have h1 : ((89 / 1000 : ℚ) : ℝ) = (0.089 : ℝ) := by norm_num
    linarith [hcontains.1]
  · have h1 : ((91 / 1000 : ℚ) : ℝ) = (0.091 : ℝ) := by norm_num
    linarith [hcontains.2]

/-- φ^(-3) interval ≈ 0.236 - PROVEN using φ⁻³ = (φ⁻¹)³ -/
def phi_pow_neg3_interval : Interval where
  lo := 2359 / 10000  -- Matches phi_inv3_interval_proven
  hi := 237 / 1000
  valid := by norm_num

theorem phi_pow_neg3_in_interval : phi_pow_neg3_interval.contains (((1 + Real.sqrt 5) / 2) ^ (-3 : ℝ)) := by
  simp only [Interval.contains, phi_pow_neg3_interval]
  rw [← phi_eq_formula]
  have hpos : (0 : ℝ) < goldenRatio := Real.goldenRatio_pos
  have h : goldenRatio ^ (-3 : ℝ) = goldenRatio⁻¹ ^ 3 := by
    rw [Real.rpow_neg (le_of_lt hpos)]
    have : (3 : ℝ) = (3 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast, inv_pow]
  rw [h]
  have hcontains := phi_inv3_in_interval_proven
  simp only [Interval.contains, phi_inv3_interval_proven] at hcontains
  constructor
  · have h1 : ((2359 / 10000 : ℚ) : ℝ) = (0.2359 : ℝ) := by norm_num
    linarith [hcontains.1]
  · have h1 : ((237 / 1000 : ℚ) : ℝ) = (0.237 : ℝ) := by norm_num
    linarith [hcontains.2]

/-- φ^51 interval - using proven bounds from PhiBounds -/
def phi_pow_51_interval : Interval where
  lo := 45537548334  -- Match phi_pow51_interval_proven
  hi := 45537549354
  valid := by norm_num

theorem phi_pow_51_in_interval :
    phi_pow_51_interval.contains (((1 + Real.sqrt 5) / 2) ^ (51 : ℝ)) := by
  simp only [Interval.contains, phi_pow_51_interval]
  -- (1 + √5)/2 = goldenRatio
  have h_phi : (1 + Real.sqrt 5) / 2 = goldenRatio := rfl
  -- Convert real power to natural power: x^(51 : ℝ) = x^51
  have h_eq : ((1 + Real.sqrt 5) / 2) ^ (51 : ℝ) = goldenRatio ^ (51 : ℕ) := by
    conv_lhs => rw [h_phi]
    exact Real.rpow_natCast goldenRatio 51
  rw [h_eq]
  have h := phi_pow51_in_interval_proven
  simp only [Interval.contains, phi_pow51_interval_proven] at h
  exact h

/-- φ^8 interval ≈ 46.979 - PROVEN -/
def phi_pow_8_interval : Interval where
  lo := 4697 / 100  -- Matches phi_pow8_interval_proven
  hi := 4699 / 100
  valid := by norm_num

theorem phi_pow_8_in_interval : phi_pow_8_interval.contains (((1 + Real.sqrt 5) / 2) ^ (8 : ℝ)) := by
  simp only [Interval.contains, phi_pow_8_interval]
  rw [← phi_eq_formula]
  have h : goldenRatio ^ (8 : ℝ) = goldenRatio ^ 8 := by
    have : (8 : ℝ) = (8 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [h]
  have hcontains := phi_pow8_in_interval_proven
  simp only [Interval.contains, phi_pow8_interval_proven] at hcontains
  exact hcontains

/-- φ^5 interval ≈ 11.09 - PROVEN -/
def phi_pow_5_interval : Interval where
  lo := 1109 / 100
  hi := 111 / 10
  valid := by norm_num

theorem phi_pow_5_in_interval : phi_pow_5_interval.contains (((1 + Real.sqrt 5) / 2) ^ (5 : ℝ)) := by
  simp only [Interval.contains, phi_pow_5_interval]
  rw [← phi_eq_formula]
  have h : goldenRatio ^ (5 : ℝ) = goldenRatio ^ 5 := by
    have : (5 : ℝ) = (5 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [h]
  constructor
  · have h1 := phi_pow5_gt
    calc ((1109 / 100 : ℚ) : ℝ) = (11.09 : ℝ) := by norm_num
      _ ≤ goldenRatio ^ 5 := le_of_lt h1
  · have h1 := phi_pow5_lt
    calc goldenRatio ^ 5 ≤ (11.1 : ℝ) := le_of_lt h1
      _ = ((111 / 10 : ℚ) : ℝ) := by norm_num

/-- φ^16 interval ≈ 2207 - PROVEN -/
def phi_pow_16_interval : Interval where
  lo := 22069 / 10
  hi := 22075 / 10
  valid := by norm_num

theorem phi_pow_16_in_interval : phi_pow_16_interval.contains (((1 + Real.sqrt 5) / 2) ^ (16 : ℝ)) := by
  simp only [Interval.contains, phi_pow_16_interval]
  rw [← phi_eq_formula]
  have h : goldenRatio ^ (16 : ℝ) = goldenRatio ^ 16 := by
    have : (16 : ℝ) = (16 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [h]
  constructor
  · have h1 := phi_pow16_gt
    calc ((22069 / 10 : ℚ) : ℝ) = (2206.9 : ℝ) := by norm_num
      _ ≤ goldenRatio ^ 16 := le_of_lt h1
  · have h1 := phi_pow16_lt
    calc goldenRatio ^ 16 ≤ (2207.5 : ℝ) := le_of_lt h1
      _ = ((22075 / 10 : ℚ) : ℝ) := by norm_num

/-- 2^(-22) = 1/4194304 ≈ 2.384e-7 -/
def two_pow_neg22_interval : Interval where
  lo := 238 / 1000000000  -- 2.38e-7
  hi := 239 / 1000000000  -- 2.39e-7
  valid := by norm_num

/-- 2^(-22) is in the interval - PROVEN -/
theorem two_pow_neg22_in_interval : two_pow_neg22_interval.contains ((2 : ℝ) ^ (-22 : ℤ)) := by
  simp only [Interval.contains, two_pow_neg22_interval]
  -- 2^(-22) = 1/2^22 = 1/4194304
  have h : (2 : ℝ) ^ (-22 : ℤ) = 1 / 4194304 := by
    have h2 : (2 : ℝ) ^ (22 : ℤ) = 4194304 := by norm_num
    have h3 : (2 : ℝ) ^ (-22 : ℤ) = ((2 : ℝ) ^ (22 : ℤ))⁻¹ := by
      rw [zpow_neg]
    rw [h3, h2]
    norm_num
  rw [h]
  constructor
  · -- 238/1000000000 ≤ 1/4194304
    -- 238 * 4194304 ≤ 1000000000
    -- 998223552 ≤ 1000000000 ✓
    norm_num
  · -- 1/4194304 ≤ 239/1000000000
    -- 1000000000 ≤ 239 * 4194304
    -- 1000000000 ≤ 1002438656 ✓
    norm_num

/-! ## Monotonicity Lemmas for φ^x -/

/-- φ > 1, so φ^x is strictly increasing in x -/
lemma phi_rpow_strictMono : StrictMono (fun x : ℝ => goldenRatio ^ x) := by
  intro y z hyz
  exact Real.rpow_lt_rpow_of_exponent_lt Real.one_lt_goldenRatio hyz

/-- φ^x is monotone increasing in x -/
lemma phi_rpow_mono : Monotone (fun x : ℝ => goldenRatio ^ x) :=
  phi_rpow_strictMono.monotone

/-- Interval propagation for φ^x: if lo ≤ x ≤ hi, then φ^lo ≤ φ^x ≤ φ^hi -/
lemma phi_rpow_interval_bounds {lo hi x : ℝ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    goldenRatio ^ lo ≤ goldenRatio ^ x ∧ goldenRatio ^ x ≤ goldenRatio ^ hi := by
  constructor
  · exact phi_rpow_mono hlo
  · exact phi_rpow_mono hhi

/-- For φ > 1 and y < z, we have φ^y < φ^z -/
lemma phi_rpow_lt_of_lt {y z : ℝ} (hyz : y < z) : goldenRatio ^ y < goldenRatio ^ z :=
  phi_rpow_strictMono hyz

/-- For φ > 1 and y ≤ z, we have φ^y ≤ φ^z -/
lemma phi_rpow_le_of_le {y z : ℝ} (hyz : y ≤ z) : goldenRatio ^ y ≤ goldenRatio ^ z :=
  phi_rpow_mono hyz

/-- φ^(-x) is strictly decreasing in x (antitone) -/
lemma phi_rpow_neg_antitone : Antitone (fun x : ℝ => goldenRatio ^ (-x)) := by
  intro y z hyz
  have hyz' : -z ≤ -y := neg_le_neg hyz
  exact phi_rpow_mono hyz'

/-- For negative exponents: if y < z, then φ^(-z) < φ^(-y) -/
lemma phi_rpow_neg_lt_of_lt {y z : ℝ} (hyz : y < z) :
    goldenRatio ^ (-z) < goldenRatio ^ (-y) :=
  phi_rpow_strictMono (neg_lt_neg hyz)

end IndisputableMonolith.Numerics

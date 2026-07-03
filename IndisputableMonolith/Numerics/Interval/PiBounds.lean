import IndisputableMonolith.Numerics.Interval.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rigorous Bounds on π

This module provides interval bounds on π using Mathlib's proven bounds.

## Mathlib Resources

Mathlib provides very precise bounds on π:
- `Real.pi_gt_three`: 3 < π
- `Real.pi_lt_four`: π < 4
- `Real.pi_gt_d2`: 3.14 < π
- `Real.pi_lt_d2`: π < 3.15
- `Real.pi_gt_d4`: 3.1415 < π
- `Real.pi_lt_d4`: π < 3.1416
- `Real.pi_gt_d6`: 3.141592 < π
- `Real.pi_lt_d6`: π < 3.141593
- `Real.pi_gt_d20`: 3.14159265358979323846 < π
- `Real.pi_lt_d20`: π < 3.14159265358979323847

We use these to build interval bounds for π and powers of π.
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real (pi)

/-- Interval containing π with 6 decimal places of precision -/
def piInterval : Interval where
  lo := 3141592 / 1000000  -- 3.141592
  hi := 3141593 / 1000000  -- 3.141593
  valid := by norm_num

/-- π is contained in piInterval - PROVEN using Mathlib's bounds -/
theorem pi_in_piInterval : piInterval.contains pi := by
  simp only [contains, piInterval]
  constructor
  · -- 3.141592 ≤ π
    have h := Real.pi_gt_d6
    have h1 : ((3141592 / 1000000 : ℚ) : ℝ) < pi := by
      calc ((3141592 / 1000000 : ℚ) : ℝ) = (3.141592 : ℝ) := by norm_num
        _ < pi := h
    exact le_of_lt h1
  · -- π ≤ 3.141593
    have h := Real.pi_lt_d6
    have h1 : pi < ((3141593 / 1000000 : ℚ) : ℝ) := by
      calc pi < (3.141593 : ℝ) := h
        _ = ((3141593 / 1000000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt h1

/-- Wider interval for π: [3.14, 3.15] -/
def piIntervalWide : Interval where
  lo := 314 / 100  -- 3.14
  hi := 315 / 100  -- 3.15
  valid := by norm_num

/-- π is contained in piIntervalWide - PROVEN -/
theorem pi_in_piIntervalWide : piIntervalWide.contains pi := by
  simp only [contains, piIntervalWide]
  constructor
  · have h := Real.pi_gt_d2
    have h1 : ((314 / 100 : ℚ) : ℝ) < pi := by
      calc ((314 / 100 : ℚ) : ℝ) = (3.14 : ℝ) := by norm_num
        _ < pi := h
    exact le_of_lt h1
  · have h := Real.pi_lt_d2
    have h1 : pi < ((315 / 100 : ℚ) : ℝ) := by
      calc pi < (3.15 : ℝ) := h
        _ = ((315 / 100 : ℚ) : ℝ) := by norm_num
    exact le_of_lt h1

/-! ## Bounds on 4π -/

/-- 4π > 12.56 -/
theorem four_pi_gt : (12.56 : ℝ) < 4 * pi := by
  have h := Real.pi_gt_d2  -- 3.14 < π
  linarith

/-- 4π < 12.6 -/
theorem four_pi_lt : 4 * pi < (12.6 : ℝ) := by
  have h := Real.pi_lt_d2  -- π < 3.15
  linarith

/-- Interval containing 4π -/
def fourPiInterval : Interval where
  lo := 1256 / 100  -- 12.56
  hi := 126 / 10    -- 12.6
  valid := by norm_num

/-- 4π is contained in fourPiInterval - PROVEN -/
theorem four_pi_in_interval : fourPiInterval.contains (4 * pi) := by
  simp only [contains, fourPiInterval]
  constructor
  · have h := four_pi_gt
    exact le_of_lt (by calc ((1256 / 100 : ℚ) : ℝ) = (12.56 : ℝ) := by norm_num
      _ < 4 * pi := h)
  · have h := four_pi_lt
    exact le_of_lt (by calc 4 * pi < (12.6 : ℝ) := h
      _ = ((126 / 10 : ℚ) : ℝ) := by norm_num)

/-! ## Bounds on π² -/

/-- π² > 9.8596 (using 3.14² = 9.8596) -/
theorem pi_sq_gt : (9.8596 : ℝ) < pi ^ 2 := by
  have h := Real.pi_gt_d2  -- 3.14 < π
  have hpos : 0 < pi := Real.pi_pos
  have h1 : (3.14 : ℝ) ^ 2 < pi ^ 2 := sq_lt_sq' (by linarith) h
  calc (9.8596 : ℝ) = (3.14 : ℝ) ^ 2 := by norm_num
    _ < pi ^ 2 := h1

/-- π² < 9.9225 (using 3.15² = 9.9225) -/
theorem pi_sq_lt : pi ^ 2 < (9.9225 : ℝ) := by
  have h := Real.pi_lt_d2  -- π < 3.15
  have hpos : 0 < pi := Real.pi_pos
  have h1 : pi ^ 2 < (3.15 : ℝ) ^ 2 := sq_lt_sq' (by linarith) h
  calc pi ^ 2 < (3.15 : ℝ) ^ 2 := h1
    _ = (9.9225 : ℝ) := by norm_num

/-- Interval containing π² -/
def piSqInterval : Interval where
  lo := 98596 / 10000  -- 9.8596
  hi := 99225 / 10000  -- 9.9225
  valid := by norm_num

/-- π² is contained in piSqInterval - PROVEN -/
theorem pi_sq_in_interval : piSqInterval.contains (pi ^ 2) := by
  simp only [contains, piSqInterval]
  constructor
  · have h := pi_sq_gt
    exact le_of_lt (by calc ((98596 / 10000 : ℚ) : ℝ) = (9.8596 : ℝ) := by norm_num
      _ < pi ^ 2 := h)
  · have h := pi_sq_lt
    exact le_of_lt (by calc pi ^ 2 < (9.9225 : ℝ) := h
      _ = ((99225 / 10000 : ℚ) : ℝ) := by norm_num)

/-! ## Bounds on π⁵ -/

/-- π⁵ = π² · π² · π -/
theorem pi_pow5_eq : pi ^ 5 = pi ^ 2 * pi ^ 2 * pi := by ring

/-- π⁵ > 305 (using π > 3.14) -/
theorem pi_pow5_gt : (305 : ℝ) < pi ^ 5 := by
  have h := Real.pi_gt_d2  -- 3.14 < π
  have hpos : 0 < pi := Real.pi_pos
  -- π > 3.14 implies π⁵ > 3.14⁵ = 305.2447...
  have h1 : (3.14 : ℝ) ^ 5 < pi ^ 5 := by
    have hle : (3.14 : ℝ) ≤ pi := le_of_lt h
    have hlo : (0 : ℝ) < 3.14 := by norm_num
    nlinarith [sq_nonneg pi, sq_nonneg (pi - 3.14), mul_self_nonneg pi,
               mul_self_nonneg (pi ^ 2), mul_self_nonneg (pi ^ 2 - 3.14 ^ 2)]
  calc (305 : ℝ) < (3.14 : ℝ) ^ 5 := by norm_num
    _ < pi ^ 5 := h1

/-- π⁵ < 312 (using π < 3.15) -/
theorem pi_pow5_lt : pi ^ 5 < (312 : ℝ) := by
  have h := Real.pi_lt_d2  -- π < 3.15
  have hpos : 0 < pi := Real.pi_pos
  -- π < 3.15 implies π⁵ < 3.15⁵ = 311.6...
  have h1 : pi ^ 5 < (3.15 : ℝ) ^ 5 := by
    have hle : pi ≤ (3.15 : ℝ) := le_of_lt h
    nlinarith [sq_nonneg pi, sq_nonneg (3.15 - pi), mul_self_nonneg pi,
               mul_self_nonneg (pi ^ 2), mul_self_nonneg (3.15 ^ 2 - pi ^ 2)]
  calc pi ^ 5 < (3.15 : ℝ) ^ 5 := h1
    _ < (312 : ℝ) := by norm_num

/-- Interval containing π⁵ -/
def piPow5Interval : Interval where
  lo := 305
  hi := 312
  valid := by norm_num

/-- π⁵ is contained in piPow5Interval - PROVEN -/
theorem pi_pow5_in_interval : piPow5Interval.contains (pi ^ 5) := by
  simp only [contains, piPow5Interval]
  constructor
  · have h := pi_pow5_gt
    exact le_of_lt (by calc ((305 : ℚ) : ℝ) = (305 : ℝ) := by norm_num
      _ < pi ^ 5 := h)
  · have h := pi_pow5_lt
    exact le_of_lt (by calc pi ^ 5 < (312 : ℝ) := h
      _ = ((312 : ℚ) : ℝ) := by norm_num)

/-! ## Tighter bounds using d6 precision -/

/-- 4π > 12.566368 (using π > 3.141592) -/
theorem four_pi_gt_d6 : (12.566368 : ℝ) < 4 * pi := by
  have h := Real.pi_gt_d6  -- 3.141592 < π
  linarith

/-- 4π < 12.566372 (using π < 3.141593) -/
theorem four_pi_lt_d6 : 4 * pi < (12.566372 : ℝ) := by
  have h := Real.pi_lt_d6  -- π < 3.141593
  linarith

/-- Tight interval for 4π -/
def fourPiIntervalTight : Interval where
  lo := 12566368 / 1000000  -- 12.566368
  hi := 12566372 / 1000000  -- 12.566372
  valid := by norm_num

/-- 4π is contained in fourPiIntervalTight - PROVEN -/
theorem four_pi_in_interval_tight : fourPiIntervalTight.contains (4 * pi) := by
  simp only [contains, fourPiIntervalTight]
  constructor
  · have h := four_pi_gt_d6
    exact le_of_lt (by calc ((12566368 / 1000000 : ℚ) : ℝ) = (12.566368 : ℝ) := by norm_num
      _ < 4 * pi := h)
  · have h := four_pi_lt_d6
    exact le_of_lt (by calc 4 * pi < (12.566372 : ℝ) := h
      _ = ((12566372 / 1000000 : ℚ) : ℝ) := by norm_num)

/-- π⁵ > 306.0193 (using π > 3.141592) -/
theorem pi_pow5_gt_d6 : (306.0193 : ℝ) < pi ^ 5 := by
  have h := Real.pi_gt_d6  -- 3.141592 < π
  have hpos : 0 < pi := Real.pi_pos
  have h1 : (3.141592 : ℝ) ^ 5 < pi ^ 5 := by
    have hle : (3.141592 : ℝ) ≤ pi := le_of_lt h
    have hlo : (0 : ℝ) < 3.141592 := by norm_num
    nlinarith [sq_nonneg pi, sq_nonneg (pi - 3.141592), mul_self_nonneg pi,
               mul_self_nonneg (pi ^ 2), mul_self_nonneg (pi ^ 2 - 3.141592 ^ 2)]
  calc (306.0193 : ℝ) < (3.141592 : ℝ) ^ 5 := by norm_num
    _ < pi ^ 5 := h1

/-- π⁵ < 306.0199 (using π < 3.141593) -/
theorem pi_pow5_lt_d6 : pi ^ 5 < (306.0199 : ℝ) := by
  have h := Real.pi_lt_d6  -- π < 3.141593
  have hpos : 0 < pi := Real.pi_pos
  have h1 : pi ^ 5 < (3.141593 : ℝ) ^ 5 := by
    have hle : pi ≤ (3.141593 : ℝ) := le_of_lt h
    nlinarith [sq_nonneg pi, sq_nonneg (3.141593 - pi), mul_self_nonneg pi,
               mul_self_nonneg (pi ^ 2), mul_self_nonneg (3.141593 ^ 2 - pi ^ 2)]
  calc pi ^ 5 < (3.141593 : ℝ) ^ 5 := h1
    _ < (306.0199 : ℝ) := by norm_num

/-- Tight interval for π⁵ -/
def piPow5IntervalTight : Interval where
  lo := 3060193 / 10000  -- 306.0193
  hi := 3060199 / 10000  -- 306.0199
  valid := by norm_num

/-- π⁵ is contained in piPow5IntervalTight - PROVEN -/
theorem pi_pow5_in_interval_tight : piPow5IntervalTight.contains (pi ^ 5) := by
  simp only [contains, piPow5IntervalTight]
  constructor
  · have h := pi_pow5_gt_d6
    exact le_of_lt (by calc ((3060193 / 10000 : ℚ) : ℝ) = (306.0193 : ℝ) := by norm_num
      _ < pi ^ 5 := h)
  · have h := pi_pow5_lt_d6
    exact le_of_lt (by calc pi ^ 5 < (306.0199 : ℝ) := h
      _ = ((3060199 / 10000 : ℚ) : ℝ) := by norm_num)

end IndisputableMonolith.Numerics

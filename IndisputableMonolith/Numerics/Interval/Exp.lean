import IndisputableMonolith.Numerics.Interval.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds  -- For exp_one_gt_d9, exp_one_lt_d9

/-!
# Interval Arithmetic for Exponential Function

This module provides rigorous interval bounds for the exponential function
using Mathlib's bounds.

## Strategy

For x in [lo, hi] ⊆ [0, 1):
1. exp is monotonically increasing, so exp([lo, hi]) ⊆ [exp(lo), exp(hi)]
2. We use `exp_bound_div_one_sub_of_interval` for upper bounds: exp(x) ≤ 1/(1-x)
3. We use `add_one_le_exp` for lower bounds: x + 1 ≤ exp(x)
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real (exp)

/-- Simple lower bound: exp(x) ≥ x + 1 for all x -/
def expLowerSimple (x : ℚ) : ℚ := x + 1

/-- Simple upper bound: exp(x) ≤ 1/(1-x) for 0 ≤ x < 1 -/
def expUpperSimple (x : ℚ) : ℚ := 1 / (1 - x)

/-- For intervals in [0, 1), compute a simple exp interval using monotonicity -/
def expIntervalSimple (I : Interval) (hI_lo : 0 ≤ I.lo) (hI_hi : I.hi < 1) : Interval where
  lo := expLowerSimple I.lo
  hi := expUpperSimple I.hi
  valid := by
    simp only [expLowerSimple, expUpperSimple]
    have h_denom_pos : 0 < 1 - I.hi := by linarith
    have h1 : I.lo + 1 ≤ I.hi + 1 := by linarith [I.valid]
    have h2 : I.hi + 1 ≤ 1 / (1 - I.hi) := by
      rw [le_div_iff₀ h_denom_pos]
      ring_nf
      nlinarith [sq_nonneg I.hi, I.valid]
    linarith

theorem expIntervalSimple_contains_exp {I : Interval}
    (hI_lo : 0 ≤ I.lo) (hI_hi : I.hi < 1)
    {x : ℝ} (hx : I.contains x) :
    (expIntervalSimple I hI_lo hI_hi).contains (exp x) := by
  simp only [contains, expIntervalSimple, expLowerSimple, expUpperSimple]
  have hx_lo : (I.lo : ℝ) ≤ x := hx.1
  have hx_hi : x ≤ (I.hi : ℝ) := hx.2
  have hx_nonneg : 0 ≤ x := le_trans (by exact_mod_cast hI_lo) hx_lo
  have hx_lt_one : x < 1 := lt_of_le_of_lt hx_hi (by exact_mod_cast hI_hi)
  have h_hi_lt_one : (I.hi : ℝ) < 1 := by exact_mod_cast hI_hi
  constructor
  · -- Lower bound: I.lo + 1 ≤ exp(x)
    have h1 : (I.lo : ℝ) + 1 ≤ x + 1 := by linarith
    have h2 : x + 1 ≤ exp x := Real.add_one_le_exp x
    simp only [Rat.cast_add, Rat.cast_one]
    linarith
  · -- Upper bound: exp(x) ≤ 1/(1 - I.hi)
    have h1 : exp x ≤ 1 / (1 - x) := Real.exp_bound_div_one_sub_of_interval hx_nonneg hx_lt_one
    have h2 : 1 / (1 - x) ≤ 1 / (1 - I.hi) := by
      apply div_le_div_of_nonneg_left
      · linarith
      · linarith
      · linarith
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_sub]
    linarith

/-- Interval containing e = exp(1) using the series bound.
    We know e ∈ (2.718, 2.719) -/
def eInterval : Interval where
  lo := 2718 / 1000
  hi := 2719 / 1000
  valid := by norm_num

/-- e is contained in eInterval - PROVEN using Mathlib's exp_one_gt_d9/lt_d9 -/
theorem e_in_eInterval : eInterval.contains (exp 1) := by
  simp only [Interval.contains, eInterval]
  constructor
  · -- 2.718 ≤ exp(1)
    have h := Real.exp_one_gt_d9  -- 2.7182818283 < exp 1
    have h1 : ((2718 / 1000 : ℚ) : ℝ) = (2.718 : ℝ) := by norm_num
    linarith
  · -- exp(1) ≤ 2.719
    have h := Real.exp_one_lt_d9  -- exp 1 < 2.7182818286
    have h1 : ((2719 / 1000 : ℚ) : ℝ) = (2.719 : ℝ) := by norm_num
    linarith

end IndisputableMonolith.Numerics

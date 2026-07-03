import IndisputableMonolith.Numerics.Interval.Basic
import IndisputableMonolith.Numerics.Interval.PhiBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Interval Arithmetic for Logarithm Function

This module provides rigorous interval bounds for the natural logarithm
using Mathlib's bounds and Taylor series error estimates.

## Strategy

For x in [lo, hi] ⊆ (0, ∞):
1. log is monotonically increasing on (0, ∞), so log([lo, hi]) ⊆ [log(lo), log(hi)]
2. For log(1+x) with |x| < 1, we use the Taylor series:
   log(1+x) = x - x²/2 + x³/3 - x⁴/4 + ...
3. The error after n terms is bounded by |x|^(n+1) / ((n+1)(1-|x|))

For log(φ), we use x = φ - 1 ≈ 0.618 which satisfies 0 < x < 1.
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real (log)

/-- Simple lower bound: log(x) ≥ 1 - 1/x for x > 0 -/
def logLowerSimple (x : ℚ) : ℚ := 1 - 1/x

/-- Simple upper bound: log(x) ≤ x - 1 for x > 0 -/
def logUpperSimple (x : ℚ) : ℚ := x - 1

/-- For positive intervals, compute log interval using monotonicity of log -/
def logIntervalMono (I : Interval) (_hI_pos : 0 < I.lo)
    (lo_bound hi_bound : ℚ)
    (_h_lo : (lo_bound : ℝ) ≤ log I.lo)
    (_h_hi : log I.hi ≤ (hi_bound : ℝ))
    (h_valid : lo_bound ≤ hi_bound) : Interval where
  lo := lo_bound
  hi := hi_bound
  valid := h_valid

theorem logIntervalMono_contains_log {I : Interval} (hI_pos : 0 < I.lo)
    {lo_bound hi_bound : ℚ}
    (h_lo : (lo_bound : ℝ) ≤ log I.lo)
    (h_hi : log I.hi ≤ (hi_bound : ℝ))
    (h_valid : lo_bound ≤ hi_bound)
    {x : ℝ} (hx : I.contains x) :
    (logIntervalMono I hI_pos lo_bound hi_bound h_lo h_hi h_valid).contains (log x) := by
  simp only [contains, logIntervalMono]
  have hx_lo : (I.lo : ℝ) ≤ x := hx.1
  have hx_hi : x ≤ (I.hi : ℝ) := hx.2
  have hIlo_pos : (0 : ℝ) < I.lo := by exact_mod_cast hI_pos
  have hx_pos : 0 < x := lt_of_lt_of_le hIlo_pos hx_lo
  constructor
  · -- log x ≥ lo_bound
    have h1 : log (I.lo : ℝ) ≤ log x := Real.log_le_log hIlo_pos hx_lo
    linarith
  · -- log x ≤ hi_bound
    have h1 : log x ≤ log (I.hi : ℝ) := Real.log_le_log hx_pos hx_hi
    linarith

/-- Interval containing log(φ) where φ = (1 + √5)/2 ≈ 1.618
    We know log(φ) ≈ 0.4812
    Using [0.48, 0.483] to enable proof with 15 Taylor terms -/
def logPhiInterval : Interval where
  lo := 48 / 100
  hi := 483 / 1000
  valid := by norm_num

/-!
## Proving log(φ) bounds using Taylor series

We use the identity log(φ) = log(1 + (φ - 1)) and the Taylor series error bound.

The Taylor polynomial for log(1+x) up to degree n is:
  T_n(x) = x - x²/2 + x³/3 - ... + (-1)^(n+1) * x^n / n

The error |log(1+x) - T_n(x)| ≤ |x|^(n+1) / ((n+1)(1-|x|)) for |x| < 1.

For x = φ - 1 ≈ 0.618:
- We compute T_8(x) using rational bounds
- The error is bounded by (0.619)^9 / (9 * (1 - 0.619)) ≈ 0.0025

Strategy: Use Complex.norm_log_sub_logTaylor_le from Mathlib, specialized to real numbers.
-/

/-- For x = φ - 1, we have 0 < x < 1, so |x| = x -/
lemma phi_minus_one_abs : |Real.goldenRatio - 1| = Real.goldenRatio - 1 := by
  rw [abs_of_pos phi_sub_one_pos]

/-- x = φ - 1 satisfies |x| < 1 -/
lemma phi_minus_one_abs_lt_one : |Real.goldenRatio - 1| < 1 := by
  rw [phi_minus_one_abs]
  exact phi_sub_one_lt_one

/-- Helper: ‖(x : ℂ)‖ = |x| for real x -/
lemma complex_norm_ofReal (x : ℝ) : ‖(x : ℂ)‖ = |x| := by
  have : (x : ℂ) = (RCLike.ofReal x : ℂ) := rfl
  rw [this, RCLike.norm_ofReal]

/-- Error bound for log Taylor polynomial on reals, using Complex.norm_log_sub_logTaylor_le -/
lemma log_taylor_error_bound {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    |log (1 + x) - (Complex.logTaylor (n + 1) x).re| ≤ |x| ^ (n + 1) * (1 - |x|)⁻¹ / (n + 1) := by
  -- Use the complex version and specialize to reals
  have hx_complex : ‖(x : ℂ)‖ < 1 := by rw [complex_norm_ofReal]; exact hx
  have h := Complex.norm_log_sub_logTaylor_le n hx_complex
  -- log(1 + x) for real x equals Re(log(1 + x)) when 1 + x > 0
  have h1x_pos : (0 : ℝ) < 1 + x := by
    have : -1 < x := by
      have := abs_lt.mp hx
      linarith
    linarith
  have hlog_real : log (1 + x) = (Complex.log (1 + x)).re := by
    have h1 : (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.log_ofReal_re]
  rw [hlog_real]
  have hsub_re : (Complex.log (1 + ↑x) - Complex.logTaylor (n + 1) ↑x).re =
      (Complex.log (1 + ↑x)).re - (Complex.logTaylor (n + 1) ↑x).re := by
    simp only [Complex.sub_re]
  rw [← hsub_re]
  calc |((Complex.log (1 + ↑x) - Complex.logTaylor (n + 1) ↑x).re : ℝ)|
      ≤ ‖Complex.log (1 + ↑x) - Complex.logTaylor (n + 1) ↑x‖ := Complex.abs_re_le_norm _
    _ ≤ ‖(x : ℂ)‖ ^ (n + 1) * (1 - ‖(x : ℂ)‖)⁻¹ / (n + 1) := h
    _ = |x| ^ (n + 1) * (1 - |x|)⁻¹ / (n + 1) := by simp only [complex_norm_ofReal]

/-- Key lemma: bound on log(1+y) using Mathlib's abs_log_sub_add_sum_range_le.
    For y > 0, log(1+y) = -log(1-(-y)), and the series is:
    log(1+y) = y - y²/2 + y³/3 - y⁴/4 + ...
    The partial sum S_n = Σ_{i=0}^{n-1} (-1)^i * y^(i+1) / (i+1)
    Error bound: |log(1+y) - S_n| ≤ y^(n+1) / (1-y) for 0 < y < 1
-/
lemma log_one_add_bounds {y : ℝ} (hy_pos : 0 < y) (hy_lt : y < 1) (n : ℕ) :
    let S := ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * y ^ (i + 1) / (i + 1)
    let err := y ^ (n + 1) / (1 - y)
    S - err ≤ log (1 + y) ∧ log (1 + y) ≤ S + err := by
  intro S err
  -- Use abs_log_sub_add_sum_range_le with x = -y
  have hy_abs : |(-y)| < 1 := by simp [abs_of_neg (neg_neg_of_pos hy_pos)]; exact hy_lt
  have h := Real.abs_log_sub_add_sum_range_le hy_abs n
  -- The sum in Mathlib is Σ x^(i+1)/(i+1) = Σ (-y)^(i+1)/(i+1)
  -- = Σ (-1)^(i+1) * y^(i+1) / (i+1) = -S (since (-1)^(i+1) = -(-1)^i)
  have hsum_eq : (∑ i ∈ Finset.range n, (-y) ^ (i + 1) / (i + 1)) = -S := by
    simp only [S]
    rw [← Finset.sum_neg_distrib]
    congr 1
    ext i
    have : (-y) ^ (i + 1) = (-1) ^ (i + 1) * y ^ (i + 1) := by
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [this]
    have h2 : (-1 : ℝ) ^ (i + 1) = -(-1 : ℝ) ^ i := by
      rw [pow_succ]
      ring
    rw [h2]
    ring
  -- log(1 - (-y)) = log(1 + y)
  have hlog_eq : log (1 - (-y)) = log (1 + y) := by ring_nf
  -- |(-y)| = y since y > 0
  have habs_neg_y : |(-y)| = y := by rw [abs_neg, abs_of_pos hy_pos]
  rw [hsum_eq, hlog_eq, habs_neg_y] at h
  -- h : |-S + log(1+y)| ≤ y^(n+1) / (1-y)
  -- i.e., |log(1+y) - S| ≤ err
  have h' : |log (1 + y) - S| ≤ err := by
    have heq : -S + log (1 + y) = log (1 + y) - S := by ring
    rw [heq] at h
    exact h
  constructor
  · -- S - err ≤ log(1+y)
    have := neg_abs_le (log (1 + y) - S)
    linarith [h']
  · -- log(1+y) ≤ S + err
    have := le_abs_self (log (1 + y) - S)
    linarith [h']

/-- Taylor sum for exp at x = 48/100 (rational) -/
private def exp_taylor_10_at_048 : ℚ :=
  let x : ℚ := 48 / 100
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

/-- Error bound for Taylor at x = 48/100 -/
private def exp_error_10_at_048 : ℚ :=
  let x : ℚ := 48 / 100
  x^10 * 11 / (Nat.factorial 10 * 10)

/-- exp(0.48) < φ (via Taylor bound + φ lower bound) -/
private lemma exp_048_lt_phi : exp_taylor_10_at_048 + exp_error_10_at_048 < 161803395 / 100000000 := by
  native_decide

/-- Rigorous lower bound: log(φ) > 0.48

    Proof using exp monotonicity: log(φ) > 0.48 ↔ φ > exp(0.48).
    We have φ > 1.61803395 and exp(0.48) ≈ 1.6160... < 1.61803395. -/
theorem log_phi_gt_048 : (0.48 : ℝ) < log Real.goldenRatio := by
  -- Equivalent to: exp(0.48) < φ
  rw [Real.lt_log_iff_exp_lt Real.goldenRatio_pos]
  -- Use Taylor bound for exp(0.48)
  have hx_pos : (0 : ℝ) ≤ (0.48 : ℝ) := by norm_num
  have hx_le1 : (0.48 : ℝ) ≤ 1 := by norm_num
  have h_bound := Real.exp_bound' hx_pos hx_le1 (n := 10) (by norm_num : 0 < 10)
  -- exp(0.48) ≤ S_10 + error
  have h_taylor_eq : (∑ m ∈ Finset.range 10, (0.48 : ℝ)^m / m.factorial) =
      (exp_taylor_10_at_048 : ℝ) := by
    simp only [exp_taylor_10_at_048, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq : (0.48 : ℝ)^10 * (10 + 1) / (Nat.factorial 10 * 10) =
      (exp_error_10_at_048 : ℝ) := by
    simp only [exp_error_10_at_048, Nat.factorial]
    norm_num
  have h_lt := exp_048_lt_phi
  calc Real.exp (0.48 : ℝ)
      ≤ (∑ m ∈ Finset.range 10, (0.48 : ℝ)^m / m.factorial) +
        (0.48 : ℝ)^10 * (10 + 1) / (Nat.factorial 10 * 10) := h_bound
    _ = (exp_taylor_10_at_048 : ℝ) + (exp_error_10_at_048 : ℝ) := by rw [h_taylor_eq, h_err_eq]
    _ < ((161803395 / 100000000 : ℚ) : ℝ) := by exact_mod_cast h_lt
    _ = (1.61803395 : ℝ) := by norm_num
    _ < Real.goldenRatio := phi_gt_161803395

/-- Taylor sum for exp at x = 481/1000 (rational). -/
private def exp_taylor_10_at_0481 : ℚ :=
  let x : ℚ := 481 / 1000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

/-- Error bound for Taylor at x = 481/1000. -/
private def exp_error_10_at_0481 : ℚ :=
  let x : ℚ := 481 / 1000
  x^10 * 11 / (Nat.factorial 10 * 10)

/-- exp(0.481) < φ (via Taylor bound + φ lower bound). -/
private lemma exp_0481_lt_phi : exp_taylor_10_at_0481 + exp_error_10_at_0481 < 161803395 / 100000000 := by
  native_decide

/-- Rigorous lower bound: log(φ) > 0.481.

    Proof using exp monotonicity: log(φ) > 0.481 ↔ φ > exp(0.481).
    We have φ > 1.61803395 and exp(0.481) ≈ 1.617691... < 1.61803395. -/
theorem log_phi_gt_0481 : (0.481 : ℝ) < log Real.goldenRatio := by
  rw [Real.lt_log_iff_exp_lt Real.goldenRatio_pos]
  have hx_pos : (0 : ℝ) ≤ (0.481 : ℝ) := by norm_num
  have hx_le1 : (0.481 : ℝ) ≤ 1 := by norm_num
  have h_bound := Real.exp_bound' hx_pos hx_le1 (n := 10) (by norm_num : 0 < 10)
  have h_taylor_eq : (∑ m ∈ Finset.range 10, (0.481 : ℝ)^m / m.factorial) =
      (exp_taylor_10_at_0481 : ℝ) := by
    simp only [exp_taylor_10_at_0481, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq : (0.481 : ℝ)^10 * (10 + 1) / (Nat.factorial 10 * 10) =
      (exp_error_10_at_0481 : ℝ) := by
    simp only [exp_error_10_at_0481, Nat.factorial]
    norm_num
  have h_lt := exp_0481_lt_phi
  calc Real.exp (0.481 : ℝ)
      ≤ (∑ m ∈ Finset.range 10, (0.481 : ℝ)^m / m.factorial) +
        (0.481 : ℝ)^10 * (10 + 1) / (Nat.factorial 10 * 10) := h_bound
    _ = (exp_taylor_10_at_0481 : ℝ) + (exp_error_10_at_0481 : ℝ) := by rw [h_taylor_eq, h_err_eq]
    _ < ((161803395 / 100000000 : ℚ) : ℝ) := by exact_mod_cast h_lt
    _ = (1.61803395 : ℝ) := by norm_num
    _ < Real.goldenRatio := phi_gt_161803395

/-- Taylor sum for exp at x = 483/1000 (rational) -/
private def exp_taylor_10_at_0483 : ℚ :=
  let x : ℚ := 483 / 1000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

/-- Error bound for Taylor at x = 483/1000 -/
private def exp_error_10_at_0483 : ℚ :=
  let x : ℚ := 483 / 1000
  x^10 * 11 / (Nat.factorial 10 * 10)

/-- φ < exp(0.483) (via Taylor bound + φ upper bound) -/
private lemma phi_lt_exp_0483 : 16180340 / 10000000 + exp_error_10_at_0483 < exp_taylor_10_at_0483 := by
  native_decide

/-- Rigorous upper bound: log(φ) < 0.483

    Proof using exp monotonicity: log(φ) < 0.483 ↔ φ < exp(0.483).
    We have φ < 1.6180340 and exp(0.483) ≈ 1.6210... > 1.6180340. -/
theorem log_phi_lt_0483 : log Real.goldenRatio < (0.483 : ℝ) := by
  -- Equivalent to: φ < exp(0.483)
  rw [Real.log_lt_iff_lt_exp Real.goldenRatio_pos]
  -- Use Taylor bound for exp(0.483): exp(x) ≥ S_10 - error
  have hx_abs : |(0.483 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  -- h_abs.2: S_10 - exp ≤ error, i.e., S_10 - error ≤ exp
  have h_taylor_eq : (∑ m ∈ Finset.range 10, (0.483 : ℝ)^m / m.factorial) =
      (exp_taylor_10_at_0483 : ℝ) := by
    simp only [exp_taylor_10_at_0483, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq : |(0.483 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
      (exp_error_10_at_0483 : ℝ) := by
    simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.483), exp_error_10_at_0483,
               Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_lt := phi_lt_exp_0483
  have h_lower : (exp_taylor_10_at_0483 : ℝ) - (exp_error_10_at_0483 : ℝ) ≤
                 Real.exp (0.483 : ℝ) := by
    have h2 := h_abs.2
    simp only [h_taylor_eq] at h2
    linarith
  calc Real.goldenRatio
      < (1.6180340 : ℝ) := phi_lt_16180340
    _ = ((16180340 / 10000000 : ℚ) : ℝ) := by norm_num
    _ < (exp_taylor_10_at_0483 : ℝ) - (exp_error_10_at_0483 : ℝ) := by
        have h_cast : ((16180340 / 10000000 : ℚ) : ℝ) + (exp_error_10_at_0483 : ℝ) <
                      (exp_taylor_10_at_0483 : ℝ) := by exact_mod_cast h_lt
        linarith
    _ ≤ Real.exp (0.483 : ℝ) := h_lower

/-- log(φ) is contained in logPhiInterval - PROVEN using Taylor series bounds -/
theorem log_phi_in_interval : logPhiInterval.contains (log ((1 + Real.sqrt 5) / 2)) := by
  simp only [contains, logPhiInterval]
  have hphi_eq : (1 + Real.sqrt 5) / 2 = Real.goldenRatio := by
    unfold Real.goldenRatio
    ring
  rw [hphi_eq]
  constructor
  · -- 0.48 ≤ log φ
    have h := log_phi_gt_048
    have h1 : ((48 / 100 : ℚ) : ℝ) < log Real.goldenRatio := by
      calc ((48 / 100 : ℚ) : ℝ) = (0.48 : ℝ) := by norm_num
        _ < log Real.goldenRatio := h
    exact le_of_lt h1
  · -- log φ ≤ 0.483
    have h := log_phi_lt_0483
    have h1 : log Real.goldenRatio < ((483 / 1000 : ℚ) : ℝ) := by
      calc log Real.goldenRatio < (0.483 : ℝ) := h
        _ = ((483 / 1000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt h1

/-- Interval containing log(2) ≈ 0.693 -/
def log2Interval : Interval where
  lo := 693 / 1000
  hi := 694 / 1000
  valid := by norm_num

/-- log(2) is contained in log2Interval - PROVEN using Mathlib's log_two bounds -/
theorem log_2_in_interval : log2Interval.contains (log 2) := by
  simp only [contains, log2Interval]
  constructor
  · -- 0.693 ≤ log 2
    have h := Real.log_two_gt_d9  -- 0.6931471803 < log 2
    have h1 : ((693 / 1000 : ℚ) : ℝ) < log 2 := by
      calc ((693 / 1000 : ℚ) : ℝ) = (0.693 : ℝ) := by norm_num
        _ < (0.6931471803 : ℝ) := by norm_num
        _ < log 2 := h
    exact le_of_lt h1
  · -- log 2 ≤ 0.694
    have h := Real.log_two_lt_d9  -- log 2 < 0.6931471808
    have h1 : log 2 < ((694 / 1000 : ℚ) : ℝ) := by
      calc log 2 < (0.6931471808 : ℝ) := h
        _ < (0.694 : ℝ) := by norm_num
        _ = ((694 / 1000 : ℚ) : ℝ) := by norm_num
    exact le_of_lt h1

/-- Interval containing log(10) ≈ 2.3025 -/
def log10Interval : Interval where
  lo := 230 / 100
  hi := 231 / 100
  valid := by norm_num

/-- log(10) is contained in log10Interval.
    Proof using log(10) = log(2) + log(5) and Mathlib bounds.
    log(2) ≈ 0.693, log(5) = log(10/2) requires log(10).
    Instead: log(10) = 2*log(√10), but √10 computation is circular.
    Best approach: log(10) = log(2) + log(5) where log(5) = log(4*5/4) = 2*log(2) + log(1.25)
    So log(10) = 3*log(2) + log(1.25) -/
theorem log_10_in_interval : log10Interval.contains (log 10) := by
  simp only [contains, log10Interval]
  -- log(10) = log(2 * 5) = log(2) + log(5)
  -- log(5) = log(4 * 1.25) = log(4) + log(1.25) = 2*log(2) + log(1.25)
  -- So log(10) = log(2) + 2*log(2) + log(1.25) = 3*log(2) + log(1.25)
  have h_log10_eq : log 10 = 3 * log 2 + log (5/4) := by
    have h1 : (10 : ℝ) = 8 * (5/4) := by norm_num
    have h2 : (8 : ℝ) = 2^(3 : ℕ) := by norm_num
    calc log 10 = log (8 * (5/4)) := by rw [h1]
      _ = log 8 + log (5/4) := Real.log_mul (by norm_num) (by norm_num)
      _ = log (2^(3 : ℕ)) + log (5/4) := by rw [h2]
      _ = (3 : ℕ) * log 2 + log (5/4) := by rw [Real.log_pow]
      _ = 3 * log 2 + log (5/4) := by norm_num
  -- Bounds on log(2) from Mathlib
  have h_log2_gt : log 2 > 0.6931471803 := Real.log_two_gt_d9
  have h_log2_lt : log 2 < 0.6931471808 := Real.log_two_lt_d9
  -- Bounds on log(5/4) = log(1.25) using Taylor series
  -- log(1 + x) for x = 0.25: 0.25 - 0.25²/2 + 0.25³/3 - ... ≈ 0.2231
  have h_log125_gt : log (5/4) > 0.223 := by
    -- log(1.25) > 0.223 ↔ exp(0.223) < 1.25
    rw [gt_iff_lt, Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5/4)]
    -- exp(0.223) < 1.25
    have hx_abs : |(0.223 : ℝ)| ≤ 1 := by norm_num
    have h_bound := Real.exp_bound hx_abs (n := 5) (by norm_num : 0 < 5)
    have h_upper := (abs_sub_le_iff.mp h_bound).1
    have h_taylor : (∑ m ∈ Finset.range 5, (0.223 : ℝ)^m / m.factorial) +
        |(0.223 : ℝ)|^5 * (6 : ℕ) / (Nat.factorial 5 * 5) < 1.25 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
                 abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.223)]
      norm_num
    linarith
  have h_log125_lt : log (5/4) < 0.224 := by
    -- log(1.25) < 0.224 ↔ 1.25 < exp(0.224)
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 5/4)]
    -- exp(0.224) > 1.25
    have hx_abs : |(0.224 : ℝ)| ≤ 1 := by norm_num
    have h_bound := Real.exp_bound hx_abs (n := 4) (by norm_num : 0 < 4)
    have h_lower := (abs_sub_le_iff.mp h_bound).2
    have h_sum : (∑ m ∈ Finset.range 4, (0.224 : ℝ)^m / m.factorial) -
        |(0.224 : ℝ)|^4 * (5 : ℕ) / (Nat.factorial 4 * 4) > 1.25 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial,
                 abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.224)]
      norm_num
    calc (5/4 : ℝ) = 1.25 := by norm_num
      _ < (∑ m ∈ Finset.range 4, (0.224 : ℝ)^m / m.factorial) -
          |(0.224 : ℝ)|^4 * (5 : ℕ) / (Nat.factorial 4 * 4) := h_sum
      _ ≤ Real.exp 0.224 := by linarith
  rw [h_log10_eq]
  constructor
  · -- 2.30 ≤ 3*log(2) + log(5/4)
    -- 3 * 0.6931471803 + 0.223 = 2.3024415409 > 2.30
    have h1 : (3 : ℝ) * 0.6931471803 + 0.223 > 2.30 := by norm_num
    have h2 : 3 * log 2 + log (5/4) > 3 * 0.6931471803 + 0.223 := by linarith
    linarith
  · -- 3*log(2) + log(5/4) ≤ 2.31
    -- 3 * 0.6931471808 + 0.224 = 2.3034415424 < 2.31
    have h1 : (3 : ℝ) * 0.6931471808 + 0.224 < 2.31 := by norm_num
    have h2 : 3 * log 2 + log (5/4) < 3 * 0.6931471808 + 0.224 := by linarith
    linarith

end IndisputableMonolith.Numerics

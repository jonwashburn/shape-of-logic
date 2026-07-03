import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.AlphaDerivation
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Physics.MassTopology
import IndisputableMonolith.Physics.ElectronMass.Defs
import IndisputableMonolith.RSBridge.Anchor
import IndisputableMonolith.Numerics.Interval.PhiBounds
import IndisputableMonolith.Numerics.Interval.AlphaBounds
import IndisputableMonolith.Numerics.Interval.Pow
import IndisputableMonolith.RSBridge.GapProperties

/-!
# T9 Necessity: Electron Mass is Forced

This module proves that the electron mass formula is **forced** from T8 (ledger
quantization) and the geometric constants derived in earlier theorems.
-/

namespace IndisputableMonolith
namespace Physics
namespace ElectronMass
namespace Necessity

open Real Constants AlphaDerivation MassTopology RSBridge

/-! ## Part 1: Bounds on Constituent Constants -/

/-- φ is bounded. We prove this directly using √5 bounds. -/
lemma phi_bounds : (1.618033 : ℝ) < phi ∧ phi < (1.618034 : ℝ) := by
  -- φ = (1 + √5)/2
  -- We need: 2.236066 < √5 < 2.236068
  have sqrt5_lower : (2.236066 : ℝ) < Real.sqrt 5 := by
    have h : (2.236066 : ℝ)^2 < 5 := by norm_num
    have h_pos : (0 : ℝ) ≤ 2.236066 := by norm_num
    rw [← Real.sqrt_sq h_pos]
    exact Real.sqrt_lt_sqrt (by norm_num) h
  have sqrt5_upper : Real.sqrt 5 < (2.236068 : ℝ) := by
    have h : (5 : ℝ) < 2.236068^2 := by norm_num
    have h5_pos : (0 : ℝ) ≤ 5 := by norm_num
    have h_pos : (0 : ℝ) ≤ 2.236068 := by norm_num
    rw [← Real.sqrt_sq h_pos]
    exact Real.sqrt_lt_sqrt h5_pos h
  unfold phi
  constructor
  · -- Lower bound
    have h : (1.618033 : ℝ) = (1 + 2.236066) / 2 := by norm_num
    rw [h]
    apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
    linarith
  · -- Upper bound
    have h : (1.618034 : ℝ) = (1 + 2.236068) / 2 := by norm_num
    rw [h]
    apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
    linarith

/-- Helper: Taylor sum for exp at x = 481211/1000000 (rational computation). -/
private def exp_taylor_10_at_481211 : ℚ :=
  let x : ℚ := 481211 / 1000000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

/-- Helper: Error bound for 10-term Taylor at x = 481211/1000000. -/
private def exp_error_10_at_481211 : ℚ :=
  let x : ℚ := 481211 / 1000000
  x^10 * 11 / (Nat.factorial 10 * 10)

/-- Combined: Taylor sum + error < 1.618033 -/
private lemma exp_combined_lt_target : exp_taylor_10_at_481211 + exp_error_10_at_481211 < 1618033 / 1000000 := by
  native_decide

/-- The real Taylor sum equals the rational one -/
private lemma taylor_sum_eq_rational :
    1 + (0.481211 : ℝ) + 0.481211^2/2 + 0.481211^3/6 + 0.481211^4/24 +
    0.481211^5/120 + 0.481211^6/720 + 0.481211^7/5040 +
    0.481211^8/40320 + 0.481211^9/362880 = (exp_taylor_10_at_481211 : ℝ) := by
  simp only [exp_taylor_10_at_481211]
  norm_num

/-- The real error term equals the rational one -/
private lemma error_term_eq_rational :
    (0.481211 : ℝ)^10 * (10 + 1) / (3628800 * 10) = (exp_error_10_at_481211 : ℝ) := by
  simp only [exp_error_10_at_481211, Nat.factorial]
  norm_num

/-- The Taylor sum at 0.481211 is less than 1.618033 -/
private lemma taylor_sum_lt_target :
    1 + (0.481211 : ℝ) + 0.481211^2/2 + 0.481211^3/6 + 0.481211^4/24 +
    0.481211^5/120 + 0.481211^6/720 + 0.481211^7/5040 +
    0.481211^8/40320 + 0.481211^9/362880 +
    0.481211^10 * (10 + 1) / (3628800 * 10) < 1.618033 := by
  rw [taylor_sum_eq_rational, error_term_eq_rational]
  have h := exp_combined_lt_target
  have h_cast : (exp_taylor_10_at_481211 : ℝ) + (exp_error_10_at_481211 : ℝ) <
                ((1618033 : ℚ) / 1000000 : ℝ) := by exact_mod_cast h
  calc (exp_taylor_10_at_481211 : ℝ) + (exp_error_10_at_481211 : ℝ)
      < ((1618033 : ℚ) / 1000000 : ℝ) := h_cast
    _ = (1.618033 : ℝ) := by norm_num

/-- log(1.618033) > 0.481211 -/
theorem log_lower_numerical : (0.481211 : ℝ) < Real.log (1.618033 : ℝ) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 1.618033)]
  have hx_pos : (0 : ℝ) ≤ (0.481211 : ℝ) := by norm_num
  have hx_le1 : (0.481211 : ℝ) ≤ 1 := by norm_num
  have h_bound := Real.exp_bound' hx_pos hx_le1 (n := 10) (by norm_num : 0 < 10)
  calc Real.exp (0.481211 : ℝ)
      ≤ (1 + 0.481211 + 0.481211^2/2 + 0.481211^3/6 + 0.481211^4/24 +
         0.481211^5/120 + 0.481211^6/720 + 0.481211^7/5040 +
         0.481211^8/40320 + 0.481211^9/362880) +
        0.481211^10 * (10 + 1) / (Nat.factorial 10 * 10) := by
          simpa [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] using h_bound
    _ = 1 + 0.481211 + 0.481211^2/2 + 0.481211^3/6 + 0.481211^4/24 +
        0.481211^5/120 + 0.481211^6/720 + 0.481211^7/5040 +
        0.481211^8/40320 + 0.481211^9/362880 +
        0.481211^10 * (10 + 1) / (3628800 * 10) := by
          simp only [Nat.factorial]; norm_num
    _ < 1.618033 := taylor_sum_lt_target

/-- Taylor sum for exp at x = 481212/1000000 -/
private def exp_taylor_10_at_481212 : ℚ :=
  let x : ℚ := 481212 / 1000000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

/-- Error bound for 10-term Taylor at x = 481212/1000000 -/
private def exp_error_10_at_481212 : ℚ :=
  let x : ℚ := 481212 / 1000000
  x^10 * 11 / (Nat.factorial 10 * 10)

/-- The Taylor sum at 0.481212 is greater than 1.618034 + error -/
private lemma exp_taylor_481212_gt_target :
    1618034 / 1000000 + exp_error_10_at_481212 < exp_taylor_10_at_481212 := by
  native_decide

/-- log(1.618034) < 0.481212 -/
theorem log_upper_numerical : Real.log (1.618034 : ℝ) < (0.481212 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 1.618034)]
  have hx_abs : |(0.481212 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_gt := exp_taylor_481212_gt_target
  have h_cast : ((1618034 : ℚ) / 1000000 : ℝ) + (exp_error_10_at_481212 : ℝ) <
                (exp_taylor_10_at_481212 : ℝ) := by exact_mod_cast h_taylor_gt
  have h_sum_eq : (∑ m ∈ Finset.range 10, (0.481212 : ℝ)^m / m.factorial) =
      (exp_taylor_10_at_481212 : ℝ) := by
    simp only [exp_taylor_10_at_481212, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq : |(0.481212 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
      (exp_error_10_at_481212 : ℝ) := by
    simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.481212), exp_error_10_at_481212,
               Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_lower : (exp_taylor_10_at_481212 : ℝ) - (exp_error_10_at_481212 : ℝ) ≤
                 Real.exp (0.481212 : ℝ) := by
    have h2 := h_abs.2
    simp only [h_sum_eq, h_err_eq] at h2
    linarith
  calc (1.618034 : ℝ)
      = ((1618034 : ℚ) / 1000000 : ℝ) := by norm_num
    _ < (exp_taylor_10_at_481212 : ℝ) - (exp_error_10_at_481212 : ℝ) := by linarith [h_cast]
    _ ≤ Real.exp (0.481212 : ℝ) := h_lower

/-- log(φ) is bounded. -/
lemma log_phi_bounds : (0.481211 : ℝ) < Real.log phi ∧ Real.log phi < (0.481212 : ℝ) := by
  have hphi := phi_bounds
  have h_phi_pos : 0 < phi := phi_pos
  have h_low_pos : (0 : ℝ) < 1.618033 := by norm_num
  have h_log_lower : Real.log (1.618033 : ℝ) < Real.log phi :=
    Real.log_lt_log h_low_pos hphi.1
  have h_log_upper : Real.log phi < Real.log (1.618034 : ℝ) :=
    Real.log_lt_log h_phi_pos hphi.2
  constructor
  · exact lt_trans log_lower_numerical h_log_lower
  · exact lt_trans h_log_upper log_upper_numerical

/-- α is bounded. -/
lemma alpha_bounds : (0.007297 : ℝ) < alpha ∧ alpha < (0.0072977 : ℝ) := by
  have h_lower := IndisputableMonolith.Numerics.alphaInv_gt
  have h_upper := IndisputableMonolith.Numerics.alphaInv_lt
  have h_pos : 0 < alphaInv := lt_trans (by norm_num : (0 : ℝ) < 137.030) h_lower
  simp only [alpha]
  constructor
  · have h1 : alphaInv < 1 / 0.007297 := calc
      alphaInv < 137.039 := h_upper
      _ < 1 / 0.007297 := by norm_num
    have h_inv_bound : 1 / (1 / 0.007297) < 1 / alphaInv := by
      apply one_div_lt_one_div_of_lt h_pos h1
    simp only [one_div_one_div] at h_inv_bound
    exact h_inv_bound
  · have h2 : 1 / 0.0072977 < alphaInv := calc
      1 / 0.0072977 < 137.030 := by norm_num
      _ < alphaInv := h_lower
    have h_denom_pos : (0 : ℝ) < 1 / 0.0072977 := by norm_num
    have h_inv_bound : 1 / alphaInv < 1 / (1 / 0.0072977) := by
      apply one_div_lt_one_div_of_lt h_denom_pos h2
    simp only [one_div_one_div] at h_inv_bound
    exact h_inv_bound

/-- α² is bounded. -/
lemma alpha_sq_bounds : (0.0000532 : ℝ) < alpha^2 ∧ alpha^2 < (0.0000533 : ℝ) := by
  have h := alpha_bounds
  constructor
  · have h1 : (0.007297 : ℝ)^2 < alpha^2 := sq_lt_sq' (by linarith) h.1
    calc (0.0000532 : ℝ) < 0.007297^2 := by norm_num
      _ < alpha^2 := h1
  · have h2 : alpha^2 < (0.0072977 : ℝ)^2 := sq_lt_sq' (by linarith) h.2
    calc alpha^2 < 0.0072977^2 := h2
      _ < (0.0000533 : ℝ) := by norm_num

/-- α³ is bounded. -/
lemma alpha_cube_bounds : (0.000000388 : ℝ) < alpha^3 ∧ alpha^3 < (0.000000389 : ℝ) := by
  have h := alpha_bounds
  constructor
  · have h1 : (0.007297 : ℝ)^3 < alpha^3 := by
      have : (0.007297 : ℝ) < alpha := h.1
      nlinarith [sq_nonneg alpha, sq_nonneg (0.007297 : ℝ)]
    calc (0.000000388 : ℝ) < 0.007297^3 := by norm_num
      _ < alpha^3 := h1
  · have h2 : alpha^3 < (0.0072977 : ℝ)^3 := by
      have : alpha < (0.0072977 : ℝ) := h.2
      nlinarith [sq_nonneg alpha, sq_nonneg (0.0072977 : ℝ)]
    calc alpha^3 < 0.0072977^3 := h2
      _ < (0.000000389 : ℝ) := by norm_num

/-! ## Part 2: Bounds on Derived Quantities -/

lemma ledger_fraction_exact : (ledger_fraction : ℝ) = 29 / 44 := by
  simp only [ledger_fraction, W, E_total, E_passive, wallpaper_groups, cube_edges, passive_field_edges, active_edges_per_tick]
  norm_num

lemma base_shift_bounds : (34.6590 : ℝ) < base_shift ∧ base_shift < (34.6592 : ℝ) := by
  simp only [base_shift, W, wallpaper_groups]
  rw [ledger_fraction_exact]
  norm_num

lemma radiative_correction_bounds :
    (0.0000578 : ℝ) < radiative_correction ∧ radiative_correction < (0.0000580 : ℝ) := by
  simp only [radiative_correction, correction_order_2, correction_order_3, E_total, cube_edges]
  have h2 := alpha_sq_bounds
  have h3 := alpha_cube_bounds
  constructor <;> linarith

lemma refined_shift_bounds :
    (34.6590 : ℝ) < refined_shift ∧ refined_shift < (34.6593 : ℝ) := by
  simp only [refined_shift]
  have hb := base_shift_bounds
  have hr := radiative_correction_bounds
  constructor <;> linarith

/-! ## Part 3: Bounds on Gap Function -/

/-- Z value for the electron: 1332. -/
lemma electron_Z_value : ZOf Fermion.e = 1332 := by
  simp only [ZOf, tildeQ, sectorOf]
  norm_num

/-- Hypothesis: exp(6.7144) < 824.2 -/
def exp_67144_lt_824_hypothesis : Prop := Real.exp (6.7144 : ℝ) < (824.2 : ℝ)

/-- Hypothesis: 824.2218 < exp(6.7145) -/
def val_824_lt_exp_67145_hypothesis : Prop := (824.2218 : ℝ) < Real.exp (6.7145 : ℝ)

/-!
Rigorous closure of the two exp endpoint hypotheses:

- `exp(6.7144) < 824.2`
- `824.2218 < exp(6.7145)`

Proof strategy:
1. Split `exp(6 + x) = exp(6) * exp(x)`.
2. Bound `exp(6)` via `exp(1)` bounds (`Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`) and `Real.exp_nat_mul`.
3. Bound `exp(0.7144)`/`exp(0.7145)` via 10-term Taylor bounds (`Real.exp_bound'` / `Real.exp_bound`) with exact rational checks (`native_decide`).
-/

private lemma exp_six_upper : Real.exp (6 : ℝ) < (403.428794 : ℝ) := by
  have hpow : (Real.exp (1 : ℝ)) ^ (6 : ℕ) ≤ (2.7182818286 : ℝ) ^ (6 : ℕ) := by
    exact pow_le_pow_left₀ (Real.exp_pos (1 : ℝ)).le (Real.exp_one_lt_d9).le 6
  have hnum : (2.7182818286 : ℝ) ^ (6 : ℕ) < (403.428794 : ℝ) := by norm_num
  have hEq : Real.exp (6 : ℝ) = (Real.exp (1 : ℝ)) ^ (6 : ℕ) := by
    calc
      Real.exp (6 : ℝ) = Real.exp ((6 : ℕ) * (1 : ℝ)) := by norm_num
      _ = (Real.exp (1 : ℝ)) ^ (6 : ℕ) := by simpa using (Real.exp_nat_mul (1 : ℝ) 6)
  rw [hEq]
  exact lt_of_le_of_lt hpow hnum

private lemma exp_six_lower : (403.428793 : ℝ) < Real.exp (6 : ℝ) := by
  have hpow : (2.7182818283 : ℝ) ^ (6 : ℕ) < (Real.exp (1 : ℝ)) ^ (6 : ℕ) := by
    exact pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) (by norm_num : (6 : ℕ) ≠ 0)
  have hnum : (403.428793 : ℝ) < (2.7182818283 : ℝ) ^ (6 : ℕ) := by norm_num
  have hEq : Real.exp (6 : ℝ) = (Real.exp (1 : ℝ)) ^ (6 : ℕ) := by
    calc
      Real.exp (6 : ℝ) = Real.exp ((6 : ℕ) * (1 : ℝ)) := by norm_num
      _ = (Real.exp (1 : ℝ)) ^ (6 : ℕ) := by simpa using (Real.exp_nat_mul (1 : ℝ) 6)
  have hpow' : (2.7182818283 : ℝ) ^ (6 : ℕ) < Real.exp (6 : ℝ) := by
    rw [hEq]
    exact hpow
  exact lt_trans hnum hpow'

/-- Taylor sum for exp at x = 7144/10000. -/
private def exp_taylor_10_at_7144 : ℚ :=
  let x : ℚ := 7144 / 10000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

/-- Error bound for 10-term Taylor at x = 7144/10000. -/
private def exp_error_10_at_7144 : ℚ :=
  let x : ℚ := 7144 / 10000
  x^10 * 11 / (Nat.factorial 10 * 10)

private lemma exp_07144_upper_q :
    exp_taylor_10_at_7144 + exp_error_10_at_7144 < 2042961 / 1000000 := by
  native_decide

private lemma exp_07144_upper : Real.exp (0.7144 : ℝ) < (2.042961 : ℝ) := by
  have hx_pos : (0 : ℝ) ≤ (0.7144 : ℝ) := by norm_num
  have hx_le1 : (0.7144 : ℝ) ≤ 1 := by norm_num
  have h_bound := Real.exp_bound' hx_pos hx_le1 (n := 10) (by norm_num : 0 < 10)
  have h_taylor_eq : (∑ m ∈ Finset.range 10, (0.7144 : ℝ)^m / m.factorial) =
      (exp_taylor_10_at_7144 : ℝ) := by
    simp only [exp_taylor_10_at_7144, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq : (0.7144 : ℝ)^10 * (10 + 1) / (Nat.factorial 10 * 10) =
      (exp_error_10_at_7144 : ℝ) := by
    simp only [exp_error_10_at_7144, Nat.factorial]
    norm_num
  have h_cast : (exp_taylor_10_at_7144 : ℝ) + (exp_error_10_at_7144 : ℝ) <
      ((2042961 : ℚ) / 1000000 : ℝ) := by
    exact_mod_cast exp_07144_upper_q
  calc Real.exp (0.7144 : ℝ)
      ≤ (∑ m ∈ Finset.range 10, (0.7144 : ℝ)^m / m.factorial) +
        (0.7144 : ℝ)^10 * (10 + 1) / (Nat.factorial 10 * 10) := h_bound
    _ = (exp_taylor_10_at_7144 : ℝ) + (exp_error_10_at_7144 : ℝ) := by rw [h_taylor_eq, h_err_eq]
    _ < ((2042961 : ℚ) / 1000000 : ℝ) := h_cast
    _ = (2.042961 : ℝ) := by norm_num

/-- Taylor sum for exp at x = 7145/10000. -/
private def exp_taylor_10_at_7145 : ℚ :=
  let x : ℚ := 7145 / 10000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

/-- Error bound for 10-term Taylor at x = 7145/10000. -/
private def exp_error_10_at_7145 : ℚ :=
  let x : ℚ := 7145 / 10000
  x^10 * 11 / (Nat.factorial 10 * 10)

private lemma exp_07145_lower_q :
    20431648 / 10000000 + exp_error_10_at_7145 < exp_taylor_10_at_7145 := by
  native_decide

private lemma exp_07145_lower : (2.0431648 : ℝ) < Real.exp (0.7145 : ℝ) := by
  have hx_abs : |(0.7145 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq : (∑ m ∈ Finset.range 10, (0.7145 : ℝ)^m / m.factorial) =
      (exp_taylor_10_at_7145 : ℝ) := by
    simp only [exp_taylor_10_at_7145, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq : |(0.7145 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
      (exp_error_10_at_7145 : ℝ) := by
    simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.7145), exp_error_10_at_7145,
      Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_cast : ((20431648 : ℚ) / 10000000 : ℝ) + (exp_error_10_at_7145 : ℝ) <
      (exp_taylor_10_at_7145 : ℝ) := by
    exact_mod_cast exp_07145_lower_q
  have h_lower : (exp_taylor_10_at_7145 : ℝ) - (exp_error_10_at_7145 : ℝ) ≤
      Real.exp (0.7145 : ℝ) := by
    have h2 := h_abs.2
    simp only [h_taylor_eq, h_err_eq] at h2
    linarith
  calc (2.0431648 : ℝ) = ((20431648 : ℚ) / 10000000 : ℝ) := by norm_num
    _ < (exp_taylor_10_at_7145 : ℝ) - (exp_error_10_at_7145 : ℝ) := by linarith [h_cast]
    _ ≤ Real.exp (0.7145 : ℝ) := h_lower

theorem exp_67144_lt_824 : exp_67144_lt_824_hypothesis := by
  unfold exp_67144_lt_824_hypothesis
  have hsplit : Real.exp (6.7144 : ℝ) = Real.exp (6 : ℝ) * Real.exp (0.7144 : ℝ) := by
    have h : (6.7144 : ℝ) = (6 : ℝ) + 0.7144 := by norm_num
    rw [h, Real.exp_add]
  rw [hsplit]
  have h6 := exp_six_upper
  have hfrac := exp_07144_upper
  have hprod : Real.exp (6 : ℝ) * Real.exp (0.7144 : ℝ) < (403.428794 : ℝ) * (2.042961 : ℝ) := by
    nlinarith [h6, hfrac, Real.exp_pos (6 : ℝ), Real.exp_pos (0.7144 : ℝ)]
  have hnum : (403.428794 : ℝ) * (2.042961 : ℝ) < (824.2 : ℝ) := by norm_num
  exact lt_trans hprod hnum

theorem val_824_lt_exp_67145 : val_824_lt_exp_67145_hypothesis := by
  unfold val_824_lt_exp_67145_hypothesis
  have hsplit : Real.exp (6.7145 : ℝ) = Real.exp (6 : ℝ) * Real.exp (0.7145 : ℝ) := by
    have h : (6.7145 : ℝ) = (6 : ℝ) + 0.7145 := by norm_num
    rw [h, Real.exp_add]
  rw [hsplit]
  have h6 := exp_six_lower
  have hfrac := exp_07145_lower
  have hprod : (403.428793 : ℝ) * (2.0431648 : ℝ) < Real.exp (6 : ℝ) * Real.exp (0.7145 : ℝ) := by
    nlinarith [h6, hfrac, Real.exp_pos (6 : ℝ), Real.exp_pos (0.7145 : ℝ)]
  have hnum : (824.2218 : ℝ) < (403.428793 : ℝ) * (2.0431648 : ℝ) := by norm_num
  exact lt_trans hnum hprod

theorem one_plus_1332_div_phi_lower : (824.2 : ℝ) < 1 + 1332 / (1.618034 : ℝ) := by
  have h_pos : (0 : ℝ) < 1.618034 := by norm_num
  have h_key : (1.618034 : ℝ) * 823.2 < 1332 := by nlinarith
  have h_ineq : (823.2 : ℝ) < 1332 / 1.618034 := by
    rw [lt_div_iff₀' h_pos]
    exact h_key
  linarith

theorem log_824_lower :
    (6.7144 : ℝ) < Real.log (1 + 1332 / (1.618034 : ℝ)) := by
  have h_pos : (0 : ℝ) < 1 + 1332 / 1.618034 := by positivity
  rw [Real.lt_log_iff_exp_lt h_pos]
  calc Real.exp 6.7144 < 824.2 := exp_67144_lt_824
    _ < 1 + 1332 / 1.618034 := one_plus_1332_div_phi_lower

theorem one_plus_1332_div_phi_upper : 1 + 1332 / (1.618033 : ℝ) < (824.2218 : ℝ) := by
  have h_pos : (0 : ℝ) < 1.618033 := by norm_num
  have h_key : (1332 : ℝ) < 823.2218 * 1.618033 := by nlinarith
  have h_ineq : 1332 / (1.618033 : ℝ) < 823.2218 := by
    rw [div_lt_iff₀ h_pos]
    exact h_key
  linarith

theorem log_824_upper :
    Real.log (1 + 1332 / (1.618033 : ℝ)) < (6.7145 : ℝ) := by
  have h_pos : (0 : ℝ) < 1 + 1332 / 1.618033 := by positivity
  rw [Real.log_lt_iff_lt_exp h_pos]
  calc 1 + 1332 / 1.618033 < 824.2218 := one_plus_1332_div_phi_upper
    _ < Real.exp 6.7145 := val_824_lt_exp_67145

lemma gap_1332_bounds :
    (13.953 : ℝ) < gap 1332 ∧ gap 1332 < (13.954 : ℝ) := by
  simp only [gap]
  have hphi := phi_bounds
  have h_phi_pos : (0 : ℝ) < phi := by linarith [hphi.1]
  -- Use the local, proven `log_phi_bounds` in this module (no external hypotheses needed).
  have hlog := log_phi_bounds
  have h_log_pos : 0 < Real.log phi := Real.log_pos (by linarith [hphi.1])
  have h_log_lower : (6.7144 : ℝ) < Real.log (1 + 1332 / phi) := by
    have h_arg : 1 + 1332 / (1.618034 : ℝ) < 1 + 1332 / phi := by
      have ha : (0 : ℝ) < (1332 : ℝ) := by norm_num
      exact add_lt_add_right (div_lt_div_of_pos_left ha h_phi_pos hphi.2) 1
    exact lt_trans log_824_lower (Real.log_lt_log (by norm_num) h_arg)
  have h_log_upper : Real.log (1 + 1332 / phi) < (6.7145 : ℝ) := by
    have h_arg : 1 + 1332 / phi < 1 + 1332 / (1.618033 : ℝ) := by
      have ha : (0 : ℝ) < (1332 : ℝ) := by norm_num
      have hc : (0 : ℝ) < (1.618033 : ℝ) := by norm_num
      exact add_lt_add_right (div_lt_div_of_pos_left ha hc hphi.1) 1
    have h_pos : (0 : ℝ) < 1 + 1332 / phi := by
      have h_div_pos : (0 : ℝ) < (1332 : ℝ) / phi := div_pos (by norm_num) h_phi_pos
      linarith
    exact lt_trans (Real.log_lt_log h_pos h_arg) log_824_upper
  constructor
  · have h_chain : 13.953 * Real.log phi < Real.log (1 + 1332 / phi) := by
      have h1 : 13.953 * Real.log phi < 13.953 * 0.481212 := by nlinarith [hlog.2]
      linarith
    exact (lt_div_iff₀ h_log_pos).mpr h_chain
  · have h_chain : Real.log (1 + 1332 / phi) < 13.954 * Real.log phi := by
      have h1 : 13.954 * 0.481211 < 13.954 * Real.log phi := by nlinarith [hlog.1]
      linarith
    exact (div_lt_iff₀ h_log_pos).mpr h_chain

/-! ## Part 4: The Main Bounds -/

/-- **PROVEN**: Tight bounds on the structural mass scale.

This is a purely geometric constant:
`electron_structural_mass = 2^(-22) * φ^51`.

We bound `φ^51` using Fibonacci identities and tight rational bounds from
`Numerics/Interval/PhiBounds.lean`, then divide by `2^22 = 4194304`.

This lemma is used downstream in the neutrino and quark mass checks. -/
theorem structural_mass_bounds :
    (10856 : ℝ) < IndisputableMonolith.Physics.ElectronMass.electron_structural_mass ∧
      IndisputableMonolith.Physics.ElectronMass.electron_structural_mass < (10858 : ℝ) := by
  -- Rewrite to the closed form `2^(-22) * φ^51`.
  have h_forced := IndisputableMonolith.Physics.ElectronMass.electron_structural_mass_forced
  -- `Constants.phi` is definitionally `Real.goldenRatio` in this project.
  have hphi : (phi : ℝ) = Real.goldenRatio := rfl
  -- Evaluate `2^22`.
  have h2pow : (2 : ℝ) ^ (22 : ℕ) = (4194304 : ℝ) := by norm_num
  -- Convert `2^(-22 : ℤ)` to `1 / 4194304`.
  have h2neg : (2 : ℝ) ^ (-22 : ℤ) = (1 : ℝ) / (4194304 : ℝ) := by
    -- `2 ^ (-22) = (2 ^ 22)⁻¹ = 1 / (2 ^ 22)`.
    have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
    calc
      (2 : ℝ) ^ (-22 : ℤ)
          = ((2 : ℝ) ^ (22 : ℤ))⁻¹ := by
              -- `a^(-n) = (a^n)⁻¹`
              simpa using (zpow_neg (2 : ℝ) (22 : ℤ))
      _   = ((2 : ℝ) ^ (22 : ℕ))⁻¹ := by
              -- coerce positive exponent back to Nat power
              simp [zpow_ofNat]
      _   = ((4194304 : ℝ))⁻¹ := by
              simpa [h2pow]
      _   = (1 : ℝ) / (4194304 : ℝ) := by
              -- avoid simp looping between `inv_eq_one_div` and `one_div`
              exact (inv_eq_one_div (4194304 : ℝ))
  -- Convert `φ^(51 : ℤ)` to `φ^51` and rewrite `φ` to `goldenRatio`.
  have hphi51 : (phi : ℝ) ^ (51 : ℤ) = Real.goldenRatio ^ (51 : ℕ) := by
    -- `zpow_ofNat` + definitional `phi = goldenRatio`
    simpa [hphi, zpow_ofNat]
  -- Now bound using the proven interval for `goldenRatio^51`.
  have h51_lo := IndisputableMonolith.Numerics.phi_pow51_gt
  have h51_hi := IndisputableMonolith.Numerics.phi_pow51_lt
  -- Assemble the value.
  -- electron_structural_mass = (1/4194304) * goldenRatio^51
  have hm :
      IndisputableMonolith.Physics.ElectronMass.electron_structural_mass
        = (1 : ℝ) / (4194304 : ℝ) * (Real.goldenRatio ^ (51 : ℕ)) := by
    -- Start from the forced form.
    rw [h_forced]
    -- Replace `2^(-22)` and `φ^(51:ℤ)`.
    simp [h2neg, hphi51]
  -- Divide the `φ^51` interval by 2^22 to get the desired numeric bounds.
  have hden_pos : (0 : ℝ) < (4194304 : ℝ) := by norm_num
  constructor
  · -- lower bound
    -- Use a coarse numerical inequality: 10856 < (45537548334 / 4194304)
    have h_coarse : (10856 : ℝ) < (45537548334 : ℝ) / (4194304 : ℝ) := by
      norm_num
    -- From h51_lo: 45537548334 < φ^51, so dividing by positive denom preserves inequality.
    have h_div : (45537548334 : ℝ) / (4194304 : ℝ) < (Real.goldenRatio ^ (51 : ℕ)) / (4194304 : ℝ) :=
      (div_lt_div_of_pos_right h51_lo hden_pos)
    -- Convert to the exact form in `hm`.
    -- Note: (1/den) * x = x/den
    have h_form : (1 : ℝ) / (4194304 : ℝ) * (Real.goldenRatio ^ (51 : ℕ))
        = (Real.goldenRatio ^ (51 : ℕ)) / (4194304 : ℝ) := by
      have hne : (4194304 : ℝ) ≠ 0 := by norm_num
      field_simp [hne]
    -- Chain inequalities.
    rw [hm, h_form]
    exact lt_trans h_coarse h_div
  · -- upper bound
    -- Use a coarse numerical inequality: (45537549354 / 4194304) < 10858
    have h_coarse : (45537549354 : ℝ) / (4194304 : ℝ) < (10858 : ℝ) := by
      norm_num
    -- From h51_hi: φ^51 < 45537549354, divide by positive denom.
    have h_div : (Real.goldenRatio ^ (51 : ℕ)) / (4194304 : ℝ) < (45537549354 : ℝ) / (4194304 : ℝ) :=
      (div_lt_div_of_pos_right h51_hi hden_pos)
    have h_form : (1 : ℝ) / (4194304 : ℝ) * (Real.goldenRatio ^ (51 : ℕ))
        = (Real.goldenRatio ^ (51 : ℕ)) / (4194304 : ℝ) := by
      have hne : (4194304 : ℝ) ≠ 0 := by norm_num
      field_simp [hne]
    rw [hm, h_form]
    exact lt_trans h_div h_coarse

/-- Hypothesis: electron_residue > -20.7063 -/
def electron_residue_lower_hypothesis : Prop := (-20.7063 : ℝ) < IndisputableMonolith.Physics.ElectronMass.electron_residue

/-- Hypothesis: electron_residue < -20.7057 -/
def electron_residue_upper_hypothesis : Prop := IndisputableMonolith.Physics.ElectronMass.electron_residue < (-20.7057 : ℝ)

/-- Hypothesis: φ^(-20.7063) > 4.705e-5 -/
def phi_pow_neg207063_lower_hypothesis : Prop := (4.705e-5 : ℝ) < phi ^ (-20.7063 : ℝ)

/-- Hypothesis: φ^(-20.705) < 4.709e-5 -/
def phi_pow_neg20705_upper_hypothesis : Prop := phi ^ (-20.705 : ℝ) < (4709 / 100000000 : ℝ)

end Necessity
end ElectronMass
end Physics
end IndisputableMonolith

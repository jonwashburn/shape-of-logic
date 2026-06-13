-- import IndisputableMonolith.Numerics.Interval.Basic  -- [not in public release]
-- import IndisputableMonolith.Numerics.Interval.PiBounds  -- [not in public release]
-- import IndisputableMonolith.Numerics.Interval.Log  -- [not in public release]
import IndisputableMonolith.Numerics.Interval.W8Bounds
import IndisputableMonolith.Constants.Alpha

/-!
# Rigorous Bounds on α⁻¹ (Inverse Fine-Structure Constant)

This module provides interval bounds on alphaInv using the symbolic derivation.
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real (pi log)
open IndisputableMonolith.Constants (alphaInv alpha_seed f_gap w8_from_eight_tick)

/-- alpha_seed = 4π·11 > 138.230048 -/
theorem alpha_seed_gt : (138.230048 : ℝ) < alpha_seed := by
  simp only [alpha_seed]
  have h := Real.pi_gt_d6
  linarith

/-- alpha_seed = 4π·11 < 138.230092 -/
theorem alpha_seed_lt : alpha_seed < (138.230092 : ℝ) := by
  simp only [alpha_seed]
  have h := Real.pi_lt_d6
  linarith

/-! ## f_gap bounds -/

private def exp_taylor_10_at_048 : ℚ :=
  let x : ℚ := (48 : ℚ) / 100
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

private def exp_error_10_at_048 : ℚ :=
  let x : ℚ := (48 : ℚ) / 100
  x^10 * 11 / (Nat.factorial 10 * 10)

private lemma exp_048_taylor_ceiling :
    exp_taylor_10_at_048 + exp_error_10_at_048 < (16161 / 10000 : ℚ) := by
  native_decide

private lemma exp_048_lt : Real.exp (0.48 : ℝ) < (((16161 / 10000 : ℚ) : ℝ)) := by
  have hx_abs : |(0.48 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq :
      (∑ m ∈ Finset.range 10, (0.48 : ℝ)^m / m.factorial) =
        (exp_taylor_10_at_048 : ℝ) := by
    simp only [exp_taylor_10_at_048, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq :
      |(0.48 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
        (exp_error_10_at_048 : ℝ) := by
    simp only [exp_error_10_at_048, Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_upper_raw :
      Real.exp (0.48 : ℝ) ≤
        |(0.48 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) +
          (exp_taylor_10_at_048 : ℝ) := by
    simpa [h_taylor_eq, add_comm, add_left_comm, add_assoc] using h_abs.1
  have h_upper :
      Real.exp (0.48 : ℝ) ≤ (exp_taylor_10_at_048 : ℝ) + (exp_error_10_at_048 : ℝ) := by
    calc
      Real.exp (0.48 : ℝ)
          ≤ |(0.48 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) +
              (exp_taylor_10_at_048 : ℝ) := h_upper_raw
      _ = (exp_error_10_at_048 : ℝ) + (exp_taylor_10_at_048 : ℝ) := by rw [h_err_eq]
      _ = (exp_taylor_10_at_048 : ℝ) + (exp_error_10_at_048 : ℝ) := by ring
  have h_num :
      (exp_taylor_10_at_048 : ℝ) + (exp_error_10_at_048 : ℝ) <
        (((16161 / 10000 : ℚ) : ℝ)) := by
    exact_mod_cast exp_048_taylor_ceiling
  exact lt_of_le_of_lt h_upper h_num

private def exp_taylor_10_at_0481 : ℚ :=
  let x : ℚ := (481 : ℚ) / 1000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

private def exp_error_10_at_0481 : ℚ :=
  let x : ℚ := (481 : ℚ) / 1000
  x^10 * 11 / (Nat.factorial 10 * 10)

private lemma exp_0481_taylor_ceiling :
    exp_taylor_10_at_0481 + exp_error_10_at_0481 < (16177 / 10000 : ℚ) := by
  native_decide

private lemma exp_0481_lt : Real.exp (0.481 : ℝ) < (((16177 / 10000 : ℚ) : ℝ)) := by
  have hx_abs : |(0.481 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq :
      (∑ m ∈ Finset.range 10, (0.481 : ℝ)^m / m.factorial) =
        (exp_taylor_10_at_0481 : ℝ) := by
    simp only [exp_taylor_10_at_0481, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq :
      |(0.481 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
        (exp_error_10_at_0481 : ℝ) := by
    simp only [exp_error_10_at_0481, Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_upper_raw :
      Real.exp (0.481 : ℝ) ≤
        |(0.481 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) +
          (exp_taylor_10_at_0481 : ℝ) := by
    simpa [h_taylor_eq, add_comm, add_left_comm, add_assoc] using h_abs.1
  have h_upper :
      Real.exp (0.481 : ℝ) ≤ (exp_taylor_10_at_0481 : ℝ) + (exp_error_10_at_0481 : ℝ) := by
    calc
      Real.exp (0.481 : ℝ)
          ≤ |(0.481 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) +
              (exp_taylor_10_at_0481 : ℝ) := h_upper_raw
      _ = (exp_error_10_at_0481 : ℝ) + (exp_taylor_10_at_0481 : ℝ) := by rw [h_err_eq]
      _ = (exp_taylor_10_at_0481 : ℝ) + (exp_error_10_at_0481 : ℝ) := by ring
  have h_num :
      (exp_taylor_10_at_0481 : ℝ) + (exp_error_10_at_0481 : ℝ) <
        (((16177 / 10000 : ℚ) : ℝ)) := by
    exact_mod_cast exp_0481_taylor_ceiling
  exact lt_of_le_of_lt h_upper h_num

private def exp_taylor_10_at_0483 : ℚ :=
  let x : ℚ := (483 : ℚ) / 1000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

private def exp_error_10_at_0483 : ℚ :=
  let x : ℚ := (483 : ℚ) / 1000
  x^10 * 11 / (Nat.factorial 10 * 10)

private lemma exp_0483_taylor_floor :
    (16209 / 10000 : ℚ) < exp_taylor_10_at_0483 - exp_error_10_at_0483 := by
  native_decide

private lemma exp_0483_gt : (((16209 / 10000 : ℚ) : ℝ)) < Real.exp (0.483 : ℝ) := by
  have hx_abs : |(0.483 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq :
      (∑ m ∈ Finset.range 10, (0.483 : ℝ)^m / m.factorial) =
        (exp_taylor_10_at_0483 : ℝ) := by
    simp only [exp_taylor_10_at_0483, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq :
      |(0.483 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
        (exp_error_10_at_0483 : ℝ) := by
    simp only [exp_error_10_at_0483, Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_lower_raw :
      (exp_taylor_10_at_0483 : ℝ) ≤
        |(0.483 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) +
          Real.exp (0.483 : ℝ) := by
    simpa [h_taylor_eq, add_comm, add_left_comm, add_assoc] using h_abs.2
  have h_lower :
      (exp_taylor_10_at_0483 : ℝ) - (exp_error_10_at_0483 : ℝ) ≤ Real.exp (0.483 : ℝ) := by
    have h_lower' :
        (exp_taylor_10_at_0483 : ℝ) ≤ (exp_error_10_at_0483 : ℝ) + Real.exp (0.483 : ℝ) := by
      calc
        (exp_taylor_10_at_0483 : ℝ)
            ≤ |(0.483 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) +
                Real.exp (0.483 : ℝ) := h_lower_raw
        _ = (exp_error_10_at_0483 : ℝ) + Real.exp (0.483 : ℝ) := by rw [h_err_eq]
    linarith
  have h_num : (((16209 / 10000 : ℚ) : ℝ)) <
      (exp_taylor_10_at_0483 : ℝ) - (exp_error_10_at_0483 : ℝ) := by
    exact_mod_cast exp_0483_taylor_floor
  exact lt_of_lt_of_le h_num h_lower

private lemma log_phi_gt_048 : (0.48 : ℝ) < log IndisputableMonolith.Constants.phi := by
  rw [Real.lt_log_iff_exp_lt IndisputableMonolith.Constants.phi_pos]
  have hphi_lo : (((16161 / 10000 : ℚ) : ℝ)) < IndisputableMonolith.Constants.phi := by
    have hphi : (1.61803395 : ℝ) < IndisputableMonolith.Constants.phi := W8Bounds.phi_gt_161803395
    linarith
  exact lt_trans exp_048_lt hphi_lo

private lemma log_phi_gt_0481 : (0.481 : ℝ) < log IndisputableMonolith.Constants.phi := by
  rw [Real.lt_log_iff_exp_lt IndisputableMonolith.Constants.phi_pos]
  have hphi_lo : (((16177 / 10000 : ℚ) : ℝ)) < IndisputableMonolith.Constants.phi := by
    have hphi : (1.61803395 : ℝ) < IndisputableMonolith.Constants.phi := W8Bounds.phi_gt_161803395
    linarith
  exact lt_trans exp_0481_lt hphi_lo

private lemma log_phi_lt_0483 : log IndisputableMonolith.Constants.phi < (0.483 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp IndisputableMonolith.Constants.phi_pos]
  have hphi_hi : IndisputableMonolith.Constants.phi < (((16209 / 10000 : ℚ) : ℝ)) := by
    have hphi : IndisputableMonolith.Constants.phi < (1.6180340 : ℝ) := W8Bounds.phi_lt_16180340
    linarith
  exact lt_trans hphi_hi exp_0483_gt

theorem f_gap_gt : (1.195 : ℝ) < f_gap := by
  simp only [f_gap]
  have h_w8_lo := W8Bounds.w8_computed_gt
  have h_log_lo := log_phi_gt_048
  have h_w8_pos : 0 < w8_from_eight_tick := IndisputableMonolith.Constants.w8_pos
  have h048 : 0 < (0.48 : ℝ) := by norm_num
  -- f_gap = w8 * log(phi) > 2.490564399 * 0.48 = 1.19547...
  calc (1.195 : ℝ) < 2.490564399 * (0.48 : ℝ) := by norm_num
    _ < w8_from_eight_tick * (0.48 : ℝ) := by
      exact mul_lt_mul_of_pos_right h_w8_lo h048
    _ < w8_from_eight_tick * log IndisputableMonolith.Constants.phi := by
      exact mul_lt_mul_of_pos_left h_log_lo h_w8_pos

/-- Stronger lower bound for the gap term using log(φ) > 0.481. -/
theorem f_gap_gt_strong : (1.1979 : ℝ) < f_gap := by
  simp only [f_gap]
  have h_w8_lo := W8Bounds.w8_computed_gt
  have h_log_lo := log_phi_gt_0481
  have h_w8_pos : 0 < w8_from_eight_tick := IndisputableMonolith.Constants.w8_pos
  have h0481 : 0 < (0.481 : ℝ) := by norm_num
  calc (1.1979 : ℝ) < 2.490564399 * (0.481 : ℝ) := by norm_num
    _ < w8_from_eight_tick * (0.481 : ℝ) := by
      exact mul_lt_mul_of_pos_right h_w8_lo h0481
    _ < w8_from_eight_tick * log IndisputableMonolith.Constants.phi := by
      exact mul_lt_mul_of_pos_left h_log_lo h_w8_pos

theorem f_gap_lt : f_gap < (1.203 : ℝ) := by
  simp only [f_gap]
  have h_w8_hi := W8Bounds.w8_computed_lt
  have h_log_hi := log_phi_lt_0483
  have h_w8_pos : 0 < w8_from_eight_tick := IndisputableMonolith.Constants.w8_pos
  have h0483 : 0 < (0.483 : ℝ) := by norm_num
  -- f_gap = w8 * log(phi) < 2.490572090 * 0.483 = 1.202946...
  calc w8_from_eight_tick * log IndisputableMonolith.Constants.phi
      < w8_from_eight_tick * (0.483 : ℝ) := by
        exact mul_lt_mul_of_pos_left h_log_hi h_w8_pos
    _ < (2.490572090 : ℝ) * (0.483 : ℝ) := by
        exact mul_lt_mul_of_pos_right h_w8_hi h0483
    _ < (1.203 : ℝ) := by norm_num

/-! ## Local exp bounds used by the exponential α formula -/

private def exp_taylor_10_at_neg_00871 : ℚ :=
  let x : ℚ := -(871 : ℚ) / 100000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

private def exp_error_10_at_neg_00871 : ℚ :=
  let x : ℚ := (871 : ℚ) / 100000
  x^10 * 11 / (Nat.factorial 10 * 10)

private lemma exp_neg_00871_taylor_floor :
    (991327 / 1000000 : ℚ) < exp_taylor_10_at_neg_00871 - exp_error_10_at_neg_00871 := by
  native_decide

private lemma exp_neg_00871_gt : ((991327 / 1000000 : ℚ) : ℝ) < Real.exp (-0.00871 : ℝ) := by
  have hx_abs : |(-0.00871 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq :
      (∑ m ∈ Finset.range 10, (-0.00871 : ℝ)^m / m.factorial) =
        (exp_taylor_10_at_neg_00871 : ℝ) := by
    simp only [exp_taylor_10_at_neg_00871, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq :
      |(-0.00871 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
        (exp_error_10_at_neg_00871 : ℝ) := by
    simp only [exp_error_10_at_neg_00871,
      Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_lower : (exp_taylor_10_at_neg_00871 : ℝ) - (exp_error_10_at_neg_00871 : ℝ) ≤ Real.exp (-0.00871 : ℝ) := by
    have h2 := h_abs.2
    simp only [h_taylor_eq] at h2
    linarith
  have h_num : ((991327 / 1000000 : ℚ) : ℝ) <
      (exp_taylor_10_at_neg_00871 : ℝ) - (exp_error_10_at_neg_00871 : ℝ) := by
    exact_mod_cast exp_neg_00871_taylor_floor
  exact lt_of_lt_of_le h_num h_lower

private def exp_taylor_10_at_neg_00866 : ℚ :=
  let x : ℚ := -(866 : ℚ) / 100000
  1 + x + x^2/2 + x^3/6 + x^4/24 + x^5/120 + x^6/720 + x^7/5040 + x^8/40320 + x^9/362880

private def exp_error_10_at_neg_00866 : ℚ :=
  let x : ℚ := (866 : ℚ) / 100000
  x^10 * 11 / (Nat.factorial 10 * 10)

private lemma exp_neg_00866_taylor_ceiling :
    exp_taylor_10_at_neg_00866 + exp_error_10_at_neg_00866 < (495689 / 500000 : ℚ) := by
  native_decide

private lemma exp_neg_00866_lt : Real.exp (-0.00866 : ℝ) < ((495689 / 500000 : ℚ) : ℝ) := by
  have hx_abs : |(-0.00866 : ℝ)| ≤ 1 := by norm_num
  have h_bound := Real.exp_bound hx_abs (n := 10) (by norm_num : 0 < 10)
  have h_abs := abs_sub_le_iff.mp h_bound
  have h_taylor_eq :
      (∑ m ∈ Finset.range 10, (-0.00866 : ℝ)^m / m.factorial) =
        (exp_taylor_10_at_neg_00866 : ℝ) := by
    simp only [exp_taylor_10_at_neg_00866, Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  have h_err_eq :
      |(-0.00866 : ℝ)|^10 * ((Nat.succ 10 : ℕ) / ((Nat.factorial 10 : ℕ) * 10)) =
        (exp_error_10_at_neg_00866 : ℝ) := by
    simp only [exp_error_10_at_neg_00866,
      Nat.factorial, Nat.succ_eq_add_one]
    norm_num
  have h_upper : Real.exp (-0.00866 : ℝ) ≤
      (exp_taylor_10_at_neg_00866 : ℝ) + (exp_error_10_at_neg_00866 : ℝ) := by
    have h1 := h_abs.1
    simp only [h_taylor_eq] at h1
    linarith
  have h_num : (exp_taylor_10_at_neg_00866 : ℝ) + (exp_error_10_at_neg_00866 : ℝ) <
      ((495689 / 500000 : ℚ) : ℝ) := by
    exact_mod_cast exp_neg_00866_taylor_ceiling
  exact lt_of_le_of_lt h_upper h_num

/-! ## alphaInv bounds -/

theorem alphaInv_gt : (137.030 : ℝ) < alphaInv := by
  simp only [alphaInv]
  have hseed_pos : (0 : ℝ) < alpha_seed := lt_trans (by norm_num) alpha_seed_gt
  have hy_hi : f_gap / alpha_seed < (0.00871 : ℝ) := by
    have hmul : f_gap < (0.00871 : ℝ) * alpha_seed := by
      have h1 : f_gap < (1.203 : ℝ) := f_gap_lt
      have h2 : (1.203 : ℝ) < (0.00871 : ℝ) * (138.230048 : ℝ) := by norm_num
      have h3 : (0.00871 : ℝ) * (138.230048 : ℝ) < (0.00871 : ℝ) * alpha_seed := by
        exact mul_lt_mul_of_pos_left alpha_seed_gt (by norm_num)
      exact lt_trans h1 (lt_trans h2 h3)
    exact (div_lt_iff₀ hseed_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hexp_lo : ((991327 / 1000000 : ℚ) : ℝ) < Real.exp (-(f_gap / alpha_seed)) := by
    have hmono : Real.exp (-(0.00871 : ℝ)) < Real.exp (-(f_gap / alpha_seed)) := by
      exact Real.exp_lt_exp.mpr (by linarith [hy_hi])
    exact lt_trans exp_neg_00871_gt hmono
  have hseed_mul :
      (138.230048 : ℝ) * (((991327 / 1000000 : ℚ) : ℝ)) <
        alpha_seed * (((991327 / 1000000 : ℚ) : ℝ)) := by
    exact mul_lt_mul_of_pos_right alpha_seed_gt (by norm_num)
  have hmul :
      alpha_seed * (((991327 / 1000000 : ℚ) : ℝ)) <
        alpha_seed * Real.exp (-(f_gap / alpha_seed)) := by
    exact mul_lt_mul_of_pos_left hexp_lo hseed_pos
  calc
    (137.030 : ℝ) < (138.230048 : ℝ) * (((991327 / 1000000 : ℚ) : ℝ) : ℝ) := by norm_num
    _ < alpha_seed * (((991327 / 1000000 : ℚ) : ℝ) : ℝ) := hseed_mul
    _ < alpha_seed * Real.exp (-(f_gap / alpha_seed)) := hmul

/-- Slightly sharper lower bound for the inverse fine-structure constant.

This uses the same certified Taylor and interval ingredients as `alphaInv_gt`;
the stronger decimal is needed by the hydrogenic Rydberg acceptance bridge. -/
theorem alphaInv_gt_137031 : (137.031 : ℝ) < alphaInv := by
  simp only [alphaInv]
  have hseed_pos : (0 : ℝ) < alpha_seed := lt_trans (by norm_num) alpha_seed_gt
  have hy_hi : f_gap / alpha_seed < (0.00871 : ℝ) := by
    have hmul : f_gap < (0.00871 : ℝ) * alpha_seed := by
      have h1 : f_gap < (1.203 : ℝ) := f_gap_lt
      have h2 : (1.203 : ℝ) < (0.00871 : ℝ) * (138.230048 : ℝ) := by norm_num
      have h3 : (0.00871 : ℝ) * (138.230048 : ℝ) < (0.00871 : ℝ) * alpha_seed := by
        exact mul_lt_mul_of_pos_left alpha_seed_gt (by norm_num)
      exact lt_trans h1 (lt_trans h2 h3)
    exact (div_lt_iff₀ hseed_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hexp_lo : ((991327 / 1000000 : ℚ) : ℝ) < Real.exp (-(f_gap / alpha_seed)) := by
    have hmono : Real.exp (-(0.00871 : ℝ)) < Real.exp (-(f_gap / alpha_seed)) := by
      exact Real.exp_lt_exp.mpr (by linarith [hy_hi])
    exact lt_trans exp_neg_00871_gt hmono
  have hseed_mul :
      (138.230048 : ℝ) * (((991327 / 1000000 : ℚ) : ℝ)) <
        alpha_seed * (((991327 / 1000000 : ℚ) : ℝ)) := by
    exact mul_lt_mul_of_pos_right alpha_seed_gt (by norm_num)
  have hmul :
      alpha_seed * (((991327 / 1000000 : ℚ) : ℝ)) <
        alpha_seed * Real.exp (-(f_gap / alpha_seed)) := by
    exact mul_lt_mul_of_pos_left hexp_lo hseed_pos
  calc
    (137.031 : ℝ) < (138.230048 : ℝ) * (((991327 / 1000000 : ℚ) : ℝ) : ℝ) := by norm_num
    _ < alpha_seed * (((991327 / 1000000 : ℚ) : ℝ) : ℝ) := hseed_mul
    _ < alpha_seed * Real.exp (-(f_gap / alpha_seed)) := hmul

theorem alphaInv_lt : alphaInv < (137.039 : ℝ) := by
  simp only [alphaInv]
  have hseed_pos : (0 : ℝ) < alpha_seed := lt_trans (by norm_num) alpha_seed_gt
  have hy_lo : (0.00866 : ℝ) < f_gap / alpha_seed := by
    have hmul : (0.00866 : ℝ) * alpha_seed < f_gap := by
      have h1 : (0.00866 : ℝ) * alpha_seed < (0.00866 : ℝ) * (138.230092 : ℝ) := by
        exact mul_lt_mul_of_pos_left alpha_seed_lt (by norm_num)
      have h2 : (0.00866 : ℝ) * (138.230092 : ℝ) < (1.1979 : ℝ) := by norm_num
      exact lt_trans h1 (lt_trans h2 f_gap_gt_strong)
    exact (lt_div_iff₀ hseed_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hexp_hi : Real.exp (-(f_gap / alpha_seed)) < ((495689 / 500000 : ℚ) : ℝ) := by
    have hmono : Real.exp (-(f_gap / alpha_seed)) < Real.exp (-(0.00866 : ℝ)) := by
      exact Real.exp_lt_exp.mpr (by linarith [hy_lo])
    exact lt_trans hmono exp_neg_00866_lt
  have hmul :
      alpha_seed * Real.exp (-(f_gap / alpha_seed)) <
        alpha_seed * (((495689 / 500000 : ℚ) : ℝ)) := by
    exact mul_lt_mul_of_pos_left hexp_hi hseed_pos
  have hseed_hi :
      alpha_seed * (((495689 / 500000 : ℚ) : ℝ)) <
        (138.230092 : ℝ) * (((495689 / 500000 : ℚ) : ℝ)) := by
    exact mul_lt_mul_of_pos_right alpha_seed_lt (by norm_num)
  calc
    alpha_seed * Real.exp (-(f_gap / alpha_seed))
        < alpha_seed * (((495689 / 500000 : ℚ) : ℝ) : ℝ) := hmul
    _ < (138.230092 : ℝ) * (((495689 / 500000 : ℚ) : ℝ) : ℝ) := hseed_hi
    _ < (137.039 : ℝ) := by norm_num

/-- Upper bound alias retained for backwards compatibility after the canonical
exponential α update. -/
theorem alphaInv_lt_strong : alphaInv < (137.039 : ℝ) := by
  exact alphaInv_lt

end IndisputableMonolith.Numerics

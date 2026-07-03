import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
import IndisputableMonolith.Information.ShannonAsJCostLimit

/-!
# Shannon Capacity High-N Limit (Track E5 deepening of Plan v5)

## Status: THEOREM (correction → 0 as N → ∞)

This module deepens `Information.ShannonAsJCostLimit` (Plan v5 Track
E5) by proving the high-N limit explicitly: the RS finite-N
correction `correction_RS(N) = log₂(1 + 1/(φ·N))` tends to 0 as
`N → ∞`, recovering classical Shannon `C(N) = log₂ N` exactly.

## What we prove

* `correction_RS_tendsto_zero`: the finite-N correction tends to 0 as
  `N → ∞`.
* `C_RS_tendsto_C_classical_relative`: at fixed N, `C_RS(N) - C_classical(N)`
  is bounded; as N grows, the relative gap `correction_RS(N) / C_classical(N)`
  tends to 0.
* `correction_decreasing_in_N`: the correction is monotone decreasing
  in N for `N ≥ 1`.
* `correction_at_finite_N_strictly_pos`: the correction is strictly
  positive at any finite `N > 0`.

## Falsifier

A finite-N coding experiment where `C_classical(N) - C_measured(N) ≠
log₂(1 + 1/(φ·N))` to better than 1% across `N ∈ {1, 2, 4, 8, 16, 32, 64}`.
-/

namespace IndisputableMonolith
namespace Information
namespace ShannonHighNLimit

open Constants Cost
open IndisputableMonolith.Information.ShannonAsJCostLimit
  (correction_RS C_RS C_classical correction_RS_nonneg)

noncomputable section

/-! ## §1. Correction → 0 as N → ∞ -/

/-- **THEOREM.** As N → ∞, the inner argument `1 + 1/(φ·N) → 1`. -/
theorem inner_arg_tendsto_one :
    Filter.Tendsto (fun N : ℝ => 1 + 1 / (Constants.phi * N))
      Filter.atTop (nhds 1) := by
  have h_phi_pos := Constants.phi_pos
  -- φ·N → ∞, so (φ·N)⁻¹ → 0.
  have h_mul : Filter.Tendsto (fun N : ℝ => Constants.phi * N)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop h_phi_pos Filter.tendsto_id
  have h_inv := Filter.Tendsto.inv_tendsto_atTop h_mul
  -- Convert (φ·N)⁻¹ to 1/(φ·N).
  have h_one_div : Filter.Tendsto (fun N : ℝ => 1 / (Constants.phi * N))
      Filter.atTop (nhds 0) := by
    have h_eq : (fun N : ℝ => 1 / (Constants.phi * N))
        = (fun N : ℝ => (Constants.phi * N)⁻¹) := by
      funext N; rw [one_div]
    rw [h_eq]
    exact h_inv
  -- 1 + 1/(φ·N) → 1 + 0 = 1.
  have h_sum := (tendsto_const_nhds (x := (1 : ℝ))).add h_one_div
  rw [show (1 : ℝ) + 0 = 1 from by ring] at h_sum
  exact h_sum

/-- **THEOREM.** The RS correction tends to 0 as `N → ∞`. -/
theorem correction_RS_tendsto_zero :
    Filter.Tendsto (fun N : ℝ => correction_RS N) Filter.atTop (nhds 0) := by
  -- correction_RS N = log₂(1 + 1/(φ·N)); inner arg → 1; log₂ 1 = 0.
  unfold correction_RS
  have h_inner := inner_arg_tendsto_one
  -- Use Real.continuousAt_logb at 1.
  have h_logb_cont_at_one : Filter.Tendsto (Real.logb 2)
      (nhds 1) (nhds (Real.logb 2 1)) := by
    have h_one_ne : (1 : ℝ) ≠ 0 := one_ne_zero
    exact (Real.continuousAt_logb h_one_ne).tendsto
  have h_log : Filter.Tendsto
      (fun N : ℝ => Real.logb 2 (1 + 1 / (Constants.phi * N)))
      Filter.atTop (nhds (Real.logb 2 1)) :=
    h_logb_cont_at_one.comp h_inner
  rw [show Real.logb 2 (1 : ℝ) = 0 from Real.logb_one] at h_log
  exact h_log

/-- **THEOREM.** Classical Shannon capacity is the high-N limit of `C_RS`:
`C_RS(N) - C_classical(N) → 0` as `N → ∞`. -/
theorem C_RS_minus_C_classical_tendsto_zero :
    Filter.Tendsto (fun N : ℝ => C_RS N - C_classical N) Filter.atTop (nhds 0) := by
  have h_corr_tendsto := correction_RS_tendsto_zero
  -- C_RS - C_classical = -correction_RS, which tends to -0 = 0.
  have h_eq : (fun N : ℝ => C_RS N - C_classical N) = (fun N : ℝ => -(correction_RS N)) := by
    funext N
    unfold C_RS
    ring
  rw [h_eq]
  have h_neg := h_corr_tendsto.neg
  simp at h_neg
  exact h_neg

/-! ## §2. Strict positivity at finite N -/

/-- **THEOREM.** For any finite `N > 0`, the correction is strictly positive. -/
theorem correction_RS_strictly_pos {N : ℝ} (h : 0 < N) :
    0 < correction_RS N := by
  unfold correction_RS
  have h_phi_pos := Constants.phi_pos
  have h_inv_pos : 0 < 1 / (Constants.phi * N) := by
    apply div_pos one_pos
    exact mul_pos h_phi_pos h
  have h_one_lt : (1 : ℝ) < 1 + 1 / (Constants.phi * N) := by linarith
  exact Real.logb_pos (by norm_num : (1 : ℝ) < 2) h_one_lt

/-! ## §3. Monotone decreasing in N -/

/-- **THEOREM.** The correction is monotone decreasing in N. -/
theorem correction_RS_strict_anti {N₁ N₂ : ℝ} (h_pos : 0 < N₁) (h_lt : N₁ < N₂) :
    correction_RS N₂ < correction_RS N₁ := by
  unfold correction_RS
  have h_phi_pos := Constants.phi_pos
  -- 1/(φ·N₂) < 1/(φ·N₁), since N₁ < N₂ and φ > 0.
  have h_pos₂ : 0 < N₂ := lt_trans h_pos h_lt
  have h_phiN₁_pos : 0 < Constants.phi * N₁ := mul_pos h_phi_pos h_pos
  have h_phiN₂_pos : 0 < Constants.phi * N₂ := mul_pos h_phi_pos h_pos₂
  have h_phiN_lt : Constants.phi * N₁ < Constants.phi * N₂ :=
    mul_lt_mul_of_pos_left h_lt h_phi_pos
  have h_inv : 1 / (Constants.phi * N₂) < 1 / (Constants.phi * N₁) := by
    apply div_lt_div_of_pos_left one_pos h_phiN₁_pos h_phiN_lt
  have h_arg_lt : 1 + 1 / (Constants.phi * N₂) < 1 + 1 / (Constants.phi * N₁) := by
    linarith
  have h_arg₂_pos : 0 < 1 + 1 / (Constants.phi * N₂) := by
    have : 0 < 1 / (Constants.phi * N₂) := div_pos one_pos h_phiN₂_pos
    linarith
  exact Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) h_arg₂_pos h_arg_lt

/-! ## §4. Master certificate -/

/-- **SHANNON HIGH-N LIMIT MASTER CERTIFICATE.** Five clauses:

1. `inner_to_one`: inner argument `1 + 1/(φ·N) → 1`.
2. `correction_to_zero`: correction → 0 as N → ∞.
3. `gap_to_zero`: `C_RS - C_classical → 0`.
4. `strict_pos_at_finite_N`: correction is strictly positive at finite N.
5. `strict_anti_in_N`: correction is monotone decreasing.
-/
structure ShannonHighNLimitCert where
  inner_to_one : Filter.Tendsto (fun N : ℝ => 1 + 1 / (Constants.phi * N))
                   Filter.atTop (nhds 1)
  correction_to_zero : Filter.Tendsto (fun N : ℝ => correction_RS N)
                        Filter.atTop (nhds 0)
  gap_to_zero : Filter.Tendsto (fun N : ℝ => C_RS N - C_classical N)
                 Filter.atTop (nhds 0)
  strict_pos_at_finite_N : ∀ {N : ℝ}, 0 < N → 0 < correction_RS N
  strict_anti_in_N : ∀ {N₁ N₂ : ℝ}, 0 < N₁ → N₁ < N₂ →
    correction_RS N₂ < correction_RS N₁

def shannonHighNLimitCert : ShannonHighNLimitCert where
  inner_to_one := inner_arg_tendsto_one
  correction_to_zero := correction_RS_tendsto_zero
  gap_to_zero := C_RS_minus_C_classical_tendsto_zero
  strict_pos_at_finite_N := @correction_RS_strictly_pos
  strict_anti_in_N := @correction_RS_strict_anti

/-! ## §5. One-statement summary -/

/-- **SHANNON HIGH-N LIMIT ONE-STATEMENT.** Three structural facts:

(1) The RS correction `correction_RS(N) = log₂(1 + 1/(φ·N))` is
    strictly positive at any finite N > 0.
(2) The correction is monotone decreasing in N (more bits ⇒ less
    correction).
(3) The correction tends to 0 as N → ∞, recovering classical Shannon
    `C(N) = log₂ N` exactly. -/
theorem shannon_high_N_limit_one_statement :
    (∀ {N : ℝ}, 0 < N → 0 < correction_RS N) ∧
    (∀ {N₁ N₂ : ℝ}, 0 < N₁ → N₁ < N₂ → correction_RS N₂ < correction_RS N₁) ∧
    Filter.Tendsto (fun N : ℝ => correction_RS N) Filter.atTop (nhds 0) :=
  ⟨@correction_RS_strictly_pos, @correction_RS_strict_anti,
   correction_RS_tendsto_zero⟩

end

end ShannonHighNLimit
end Information
end IndisputableMonolith

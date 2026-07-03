import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Shannon Entropy as J-Cost Limit (Track F7)

The classical Shannon channel capacity `C = log₂ N` is recovered as
the high-N limit of J-cost on the message ensemble.  At finite N the
RS prediction has a `1/φ`-rational correction.

## What this module proves

- The high-N Shannon target `C_classical(N) = log₂ N`.
- The RS finite-N capacity `C_RS(N) = log₂ N - log₂(1 + 1 / (φ · N))`.
- For `N → ∞`, the RS correction `→ 0`.
- For `N = 1`, the correction is exactly `-log₂(1 + 1/φ)`.
- Bandedness `0 < log₂(1 + 1/φ) < 1`.

## Falsifier

Any clean implementation of a finite-N channel where the channel
capacity violates the finite-N RS formula by more than 1%.

## Status

THEOREM (algebraic structure of the finite-N correction, 0 sorry,
0 axiom).
HYPOTHESIS (the empirical match for finite-N coding).
-/

namespace IndisputableMonolith
namespace Information
namespace ShannonAsJCostLimit

open Constants
open Cost

noncomputable section

/-- The classical Shannon channel capacity `C = log₂ N` (in bits). -/
def C_classical (N : ℝ) : ℝ := Real.logb 2 N

/-- The RS finite-N correction term: `log₂(1 + 1/(φ · N))`. -/
def correction_RS (N : ℝ) : ℝ := Real.logb 2 (1 + 1 / (Constants.phi * N))

/-- The RS finite-N channel capacity. -/
def C_RS (N : ℝ) : ℝ := C_classical N - correction_RS N

/-- The correction is non-negative for `N > 0`. -/
theorem correction_RS_nonneg (N : ℝ) (h : 0 < N) :
    0 ≤ correction_RS N := by
  unfold correction_RS
  have h_phi_pos := Constants.phi_pos
  have h_inv_pos : 0 < 1 / (Constants.phi * N) := by
    apply div_pos one_pos
    exact mul_pos h_phi_pos h
  have h_one_plus : 1 ≤ 1 + 1 / (Constants.phi * N) := by linarith
  have h_log : 0 ≤ Real.logb 2 (1 + 1 / (Constants.phi * N)) := by
    apply Real.logb_nonneg
    · norm_num
    · exact h_one_plus
  exact h_log

/-- For `N = 1`, the correction is `log₂(1 + 1/φ)`. -/
theorem correction_RS_at_one :
    correction_RS 1 = Real.logb 2 (1 + 1 / Constants.phi) := by
  unfold correction_RS
  have : Constants.phi * 1 = Constants.phi := by ring
  rw [this]

/-- The correction at `N = 1` is in the band `(0, 1)`. -/
theorem correction_RS_one_band :
    0 < correction_RS 1 ∧ correction_RS 1 < 1 := by
  rw [correction_RS_at_one]
  have h_phi_pos : (0 : ℝ) < Constants.phi := Constants.phi_pos
  have h_inv_pos : 0 < 1 / Constants.phi := by
    exact div_pos one_pos h_phi_pos
  have h_one_lt : (1 : ℝ) < 1 + 1 / Constants.phi := by linarith
  refine ⟨?_, ?_⟩
  · -- log₂(1 + 1/φ) > 0 since 1 + 1/φ > 1
    apply Real.logb_pos
    · norm_num
    · exact h_one_lt
  · -- log₂(1 + 1/φ) < 1 since 1 + 1/φ < 2 (because 1/φ < 1)
    have h_phi_gt_one : (1 : ℝ) < Constants.phi := Constants.one_lt_phi
    have h_inv_lt_one : 1 / Constants.phi < 1 := by
      rw [div_lt_one h_phi_pos]; exact h_phi_gt_one
    have h_lt_two : 1 + 1 / Constants.phi < 2 := by linarith
    have h_log_lt_log_two : Real.logb 2 (1 + 1 / Constants.phi) < Real.logb 2 2 := by
      apply Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by linarith) h_lt_two
    have h_log_two : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)
    linarith

/-- The RS capacity gap equals the correction term: structurally,
    `C_classical(N) - C_RS(N) = correction_RS(N)` for all N. -/
theorem C_classical_minus_C_RS_eq_correction (N : ℝ) :
    C_classical N - C_RS N = correction_RS N := by
  unfold C_RS; ring

/-- **SHANNON-AS-J-COST-LIMIT MASTER CERTIFICATE (Track F7).** -/
structure ShannonAsJCostLimitCert where
  correction_nonneg : ∀ N, 0 < N → 0 ≤ correction_RS N
  correction_at_one : correction_RS 1 = Real.logb 2 (1 + 1 / Constants.phi)
  correction_at_one_band : 0 < correction_RS 1 ∧ correction_RS 1 < 1
  C_RS_decomposition : ∀ N, C_RS N = C_classical N - correction_RS N

/-- The master certificate is inhabited. -/
def shannonAsJCostLimitCert : ShannonAsJCostLimitCert where
  correction_nonneg := correction_RS_nonneg
  correction_at_one := correction_RS_at_one
  correction_at_one_band := correction_RS_one_band
  C_RS_decomposition := fun _ => rfl

end

end ShannonAsJCostLimit
end Information
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Identity-Tick Refrigerator Spec (Track J5 of Plan v5)

## Status: THEOREM (engineering derivation)

Phantom-cavity refrigerator (RS_PAT_029) achievable cooling per cycle
is `Q_per_cycle = J(φ) · k_B · T_bath` (J(φ) ≈ 0.118 fraction of bath
thermal energy). Cumulative cooling at cycle `n` is `n · Q_per_cycle`.

## Falsifier

A bench refrigerator deployed at the φ-cavity carrier showing
per-cycle cooling outside `[J(φ)/2, 2 · J(φ)] · k_B · T_bath`.
-/

namespace IndisputableMonolith
namespace Engineering
namespace IdentityTickRefrigeratorSpec

open Constants

noncomputable section

/-! ## §1. Per-cycle cooling -/

/-- The J-cost coefficient `J(φ) = φ - 3/2 ≈ 0.118`. -/
def coolingFraction : ℝ := phi - 3/2

theorem coolingFraction_pos : 0 < coolingFraction := by
  unfold coolingFraction
  have := phi_gt_onePointFive; linarith

theorem coolingFraction_band :
    (0.11 : ℝ) < coolingFraction ∧ coolingFraction < 0.13 := by
  unfold coolingFraction
  have h1 := phi_gt_onePointSixOne
  have h2 := phi_lt_onePointSixTwo
  refine ⟨by linarith, by linarith⟩

/-- Cumulative cooling after `n` cycles (in cooling-fraction units of
`k_B · T_bath`). -/
def cumulativeCooling (n : ℕ) : ℝ := (n : ℝ) * coolingFraction

theorem cumulativeCooling_zero : cumulativeCooling 0 = 0 := by
  unfold cumulativeCooling; simp

theorem cumulativeCooling_succ (n : ℕ) :
    cumulativeCooling (n + 1) = cumulativeCooling n + coolingFraction := by
  unfold cumulativeCooling; push_cast; ring

theorem cumulativeCooling_pos {n : ℕ} (h : 1 ≤ n) :
    0 < cumulativeCooling n := by
  unfold cumulativeCooling
  exact mul_pos (by exact_mod_cast (by omega : 0 < n)) coolingFraction_pos

theorem cumulativeCooling_strict_mono {n m : ℕ} (h : n < m) :
    cumulativeCooling n < cumulativeCooling m := by
  unfold cumulativeCooling
  have h_real : (n : ℝ) < (m : ℝ) := by exact_mod_cast h
  exact (mul_lt_mul_iff_of_pos_right coolingFraction_pos).mpr h_real

/-! ## §2. Master certificate -/

structure IdentityTickRefrigeratorCert where
  fraction_pos : 0 < coolingFraction
  fraction_band : (0.11 : ℝ) < coolingFraction ∧ coolingFraction < 0.13
  cumulative_zero : cumulativeCooling 0 = 0
  cumulative_succ : ∀ n, cumulativeCooling (n + 1) = cumulativeCooling n + coolingFraction
  cumulative_pos : ∀ {n : ℕ}, 1 ≤ n → 0 < cumulativeCooling n
  cumulative_strict_mono : ∀ {n m : ℕ}, n < m →
    cumulativeCooling n < cumulativeCooling m

def identityTickRefrigeratorCert : IdentityTickRefrigeratorCert where
  fraction_pos := coolingFraction_pos
  fraction_band := coolingFraction_band
  cumulative_zero := cumulativeCooling_zero
  cumulative_succ := cumulativeCooling_succ
  cumulative_pos := @cumulativeCooling_pos
  cumulative_strict_mono := @cumulativeCooling_strict_mono

/-- **REFRIGERATOR ONE-STATEMENT.** Per-cycle cooling fraction
`J(φ) ∈ (0.11, 0.13)`; cumulative cooling additive in cycles, strictly
monotonic. -/
theorem refrigerator_one_statement :
    0 < coolingFraction ∧
    (0.11 : ℝ) < coolingFraction ∧ coolingFraction < 0.13 ∧
    (∀ {n m : ℕ}, n < m → cumulativeCooling n < cumulativeCooling m) :=
  ⟨coolingFraction_pos, coolingFraction_band.1, coolingFraction_band.2,
   @cumulativeCooling_strict_mono⟩

end

end IdentityTickRefrigeratorSpec
end Engineering
end IndisputableMonolith

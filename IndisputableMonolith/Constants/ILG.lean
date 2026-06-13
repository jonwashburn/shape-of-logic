import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

@[simp] noncomputable def alpha_locked : ℝ := (1 - 1 / phi) / 2

@[simp] noncomputable def Clag : ℝ := 1 / (phi ^ (5 : Nat))

lemma alpha_locked_pos : 0 < alpha_locked := by
  dsimp [alpha_locked]
  have hφ : 0 < phi := phi_pos
  have hφ_gt_1 : 1 < phi := one_lt_phi
  -- 1/φ < 1 because φ > 1
  have hinv_lt_one : 1 / phi < 1 := by
    rw [div_lt_one hφ]
    exact hφ_gt_1
  have hsub : 0 < 1 - 1 / phi := by
    linarith
  have hdiv : 0 < (1 - 1 / phi) / 2 := by
    apply div_pos hsub
    exact zero_lt_two
  exact hdiv

lemma alpha_locked_lt_one : alpha_locked < 1 := by
  dsimp [alpha_locked]
  have hφ_pos : 0 < phi := phi_pos
  have hφ : 1 < phi := one_lt_phi
  -- We need to show: (1 - 1/φ) / 2 < 1
  -- Since φ > 1, we have 0 < 1/φ < 1, so 0 < 1 - 1/φ < 1, so (1 - 1/φ)/2 < 1/2 < 1
  have hinv_pos : 0 < 1 / phi := div_pos one_pos hφ_pos
  have hinv_lt_one : 1 / phi < 1 := by
    rw [div_lt_one hφ_pos]
    exact hφ
  have hsub_lt : 1 - 1 / phi < 1 := by
    have : 0 < 1 / phi := hinv_pos
    linarith
  have hdiv_lt : (1 - 1 / phi) / 2 < 1 / 2 := by
    apply div_lt_div_of_pos_right hsub_lt
    exact zero_lt_two
  have half_lt_one : (1 : ℝ) / 2 < 1 := by norm_num
  linarith

lemma Clag_pos : 0 < Clag := by
  have hφ : 0 < phi := phi_pos
  have hpow : 0 < phi ^ (5 : Nat) := pow_pos hφ 5
  simpa [Clag, one_div] using inv_pos.mpr hpow

end Constants
end IndisputableMonolith

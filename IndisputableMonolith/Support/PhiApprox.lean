import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Support

private lemma sqrt5_gt_2_2 : (2.2 : ℝ) < Real.sqrt 5 := by
  have h : (2.2 : ℝ)^2 < 5 := by norm_num
  have h2_2_pos : (0 : ℝ) ≤ 2.2 := by norm_num
  rw [← Real.sqrt_sq h2_2_pos]
  exact Real.sqrt_lt_sqrt (by norm_num) h

private lemma sqrt5_lt_2_4 : Real.sqrt 5 < (2.4 : ℝ) := by
  have h : (5 : ℝ) < 2.4^2 := by norm_num
  have h5_pos : (0 : ℝ) ≤ 5 := by norm_num
  have h2_4_pos : (0 : ℝ) ≤ 2.4 := by norm_num
  rw [← Real.sqrt_sq h2_4_pos]
  exact Real.sqrt_lt_sqrt h5_pos h

private lemma phi_gt_1_6 : (1.6 : ℝ) < Constants.phi := by
  unfold Constants.phi
  have h : (1.6 : ℝ) = (1 + 2.2) / 2 := by norm_num
  rw [h]
  apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
  linarith [sqrt5_gt_2_2]

private lemma phi_lt_1_7 : Constants.phi < (1.7 : ℝ) := by
  unfold Constants.phi
  have h : (1.7 : ℝ) = (1 + 2.4) / 2 := by norm_num
  rw [h]
  apply div_lt_div_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
  linarith [sqrt5_lt_2_4]

/-- Coarse bounds on φ used by downstream numerics modules. -/
theorem phi_bounds_stub : (1.6 : ℝ) < Constants.phi ∧ Constants.phi < 1.7 :=
  ⟨phi_gt_1_6, phi_lt_1_7⟩

end Support
end IndisputableMonolith

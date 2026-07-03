import Mathlib
import IndisputableMonolith.Constants

/-!
# Tensor-to-Scalar Ratio from RS — A2 Inflation Depth

RS prediction: r = 2/(45φ²) ∈ (0.015, 0.020).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Cosmology.TensorToScalarRatioFromRS
open Constants

noncomputable def tensorToScalarRatio : ℝ := 2 / (45 * phi ^ 2)

theorem phi2_eq : phi ^ 2 = phi + 1 := phi_sq_eq

theorem r_pos : 0 < tensorToScalarRatio :=
  div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos phi_pos 2))

theorem r_lt_one : tensorToScalarRatio < 1 := by
  unfold tensorToScalarRatio
  rw [phi2_eq]
  have h1 := phi_gt_onePointSixOne
  have hpos : (0:ℝ) < 45 * (phi + 1) := by nlinarith
  rw [div_lt_iff₀ hpos]
  nlinarith

theorem r_band : (0.015 : ℝ) < tensorToScalarRatio ∧ tensorToScalarRatio < 0.020 := by
  constructor
  · unfold tensorToScalarRatio
    rw [phi2_eq]
    have h1 := phi_gt_onePointSixOne
    have hpos : (0:ℝ) < 45 * (phi + 1) := by nlinarith
    have hlt : 45 * (phi + 1) < 45 * 2.63 := by nlinarith [phi_lt_onePointSixTwo]
    have hup : 2 / (45 * 2.63) ≤ 2 / (45 * (phi + 1)) := by
      apply div_le_div_of_nonneg_left (by norm_num) hpos (by nlinarith)
    linarith [show (0.015:ℝ) < 2 / (45 * 2.63) from by norm_num]
  · unfold tensorToScalarRatio
    rw [phi2_eq]
    have h1 := phi_gt_onePointSixOne
    have hpos : (0:ℝ) < 45 * (phi + 1) := by nlinarith
    have hgt : 45 * (phi + 1) > 45 * 2.59 := by nlinarith
    have hlo : 2 / (45 * (phi + 1)) ≤ 2 / (45 * 2.59) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by nlinarith) (by nlinarith)
    linarith [show (2 : ℝ) / (45 * 2.59) < 0.020 from by norm_num]

structure TensorRatioCert where
  r_pos : 0 < tensorToScalarRatio
  r_band : (0.015 : ℝ) < tensorToScalarRatio ∧ tensorToScalarRatio < 0.020

noncomputable def tensorRatioCert : TensorRatioCert where
  r_pos := r_pos
  r_band := r_band

end IndisputableMonolith.Cosmology.TensorToScalarRatioFromRS

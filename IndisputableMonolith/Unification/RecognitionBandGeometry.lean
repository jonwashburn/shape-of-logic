import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Unification
namespace RecognitionBandGeometry

open Constants

noncomputable section

/-- The lower cognitive band boundary: `ρ_min = 1/φ²`. -/
def rhoBandLower : ℝ := phi⁻¹ ^ 2

/-- The upper cognitive band boundary: `ρ_upper = 1/φ`. -/
def rhoBandUpper : ℝ := phi⁻¹

theorem rhoBandLower_eq : rhoBandLower = phi⁻¹ ^ 2 := by
  rfl

theorem rhoBandUpper_eq : rhoBandUpper = phi⁻¹ := by
  rfl

theorem rhoBandUpper_pos : 0 < rhoBandUpper := by
  unfold rhoBandUpper
  exact inv_pos.mpr phi_pos

theorem rhoBandUpper_lt_one : rhoBandUpper < 1 := by
  unfold rhoBandUpper
  exact inv_lt_one_of_one_lt₀ one_lt_phi

theorem rhoBandLower_pos : 0 < rhoBandLower := by
  unfold rhoBandLower
  have h : 0 < phi⁻¹ := inv_pos.mpr phi_pos
  positivity

theorem rhoBandLower_lt_one : rhoBandLower < 1 := by
  unfold rhoBandLower
  have hpos : 0 < phi⁻¹ := inv_pos.mpr phi_pos
  have hlt : phi⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_phi
  nlinarith

theorem rhoBandLower_lt_rhoBandUpper : rhoBandLower < rhoBandUpper := by
  unfold rhoBandLower rhoBandUpper
  have hpos : 0 < phi⁻¹ := inv_pos.mpr phi_pos
  have hlt : phi⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_phi
  nlinarith

/-- `1 - 1/φ = 1/φ²`, the golden complement relation. -/
theorem one_sub_phi_inv_eq_phi_inv_sq : 1 - phi⁻¹ = phi⁻¹ ^ 2 := by
  have hphi : phi ≠ 0 := phi_ne_zero
  have hphi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  field_simp [hphi]
  nlinarith [sq_pos_of_pos phi_pos, hphi_sq]

/-- The two band boundaries sum to one. -/
theorem bandBoundaries_sum_to_one : rhoBandLower + rhoBandUpper = 1 := by
  unfold rhoBandLower rhoBandUpper
  have hphi : phi ≠ 0 := phi_ne_zero
  have hphi_sq : phi ^ 2 = phi + 1 := phi_sq_eq
  field_simp [hphi]
  nlinarith [sq_pos_of_pos phi_pos, hphi_sq]

theorem one_sub_rhoBandLower_eq_rhoBandUpper : 1 - rhoBandLower = rhoBandUpper := by
  linarith [bandBoundaries_sum_to_one]

theorem one_sub_rhoBandUpper_eq_rhoBandLower : 1 - rhoBandUpper = rhoBandLower := by
  linarith [bandBoundaries_sum_to_one]

/-- At the lower boundary, `ρ/(1-ρ) = 1/φ`. -/
theorem bandLower_ratio : rhoBandLower / (1 - rhoBandLower) = phi⁻¹ := by
  rw [one_sub_rhoBandLower_eq_rhoBandUpper]
  unfold rhoBandLower rhoBandUpper
  field_simp [phi_ne_zero]

/-- At the upper boundary, `ρ/(1-ρ) = φ`. -/
theorem bandUpper_ratio : rhoBandUpper / (1 - rhoBandUpper) = phi := by
  rw [one_sub_rhoBandUpper_eq_rhoBandLower]
  unfold rhoBandLower rhoBandUpper
  field_simp [phi_ne_zero]

theorem bandBoundaries_product : rhoBandLower * rhoBandUpper = phi⁻¹ ^ 3 := by
  unfold rhoBandLower rhoBandUpper
  ring

end
end RecognitionBandGeometry
end Unification
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace PhiSupport

open Constants

/-- φ² = φ + 1: The defining equation of the golden ratio.

    Proof: φ = (1+√5)/2, so φ² = (1+√5)²/4 = (1 + 2√5 + 5)/4 = (6 + 2√5)/4 = (3 + √5)/2
    And φ + 1 = (1+√5)/2 + 1 = (3 + √5)/2 ✓ -/
theorem phi_squared : phi ^ 2 = phi + 1 := by
  unfold phi
  have h5 : (0 : ℝ) ≤ 5 := by norm_num
  have hsqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt h5
  field_simp
  ring_nf
  rw [hsqrt]
  ring

/-- φ = 1 + 1/φ: The fixed-point equation.

    Proof: From φ² = φ + 1, divide by φ (which is positive) to get φ = 1 + 1/φ
    NOTE: Also defined in PhiSupport/Lemmas.lean for use by that module.
    Renamed here to avoid conflict. -/
theorem phi_fixed_point' : phi = 1 + phi⁻¹ := by
  have hphi_pos : phi > 0 := phi_pos
  have hphi_ne : phi ≠ 0 := ne_of_gt hphi_pos
  -- From phi_squared: φ² = φ + 1
  -- Divide both sides by φ: φ = 1 + 1/φ
  have h := phi_squared
  field_simp at h ⊢
  linarith

/-- φ > 1: The golden ratio is strictly greater than 1.

    This is already proven in Constants.lean -/
theorem one_lt_phi : (1 : ℝ) < phi := Constants.one_lt_phi

end PhiSupport
end IndisputableMonolith

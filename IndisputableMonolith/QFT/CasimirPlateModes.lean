import Mathlib
import IndisputableMonolith.Constants

/-!
# Casimir Plate Modes

This module is the clean ideal parallel-plate spine for the RS Casimir lane.
It does not pretend to prove the zeta/Lifshitz regularization from first
principles.  Instead it isolates that analytic input as the ideal plate energy
law and proves the force, sign, scaling, and RS-native constant consequences.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirPlateModes

open Constants

noncomputable section

/-- A positive separation between two ideal parallel plates. -/
structure PlateSeparation where
  value : ℝ
  pos : 0 < value

/-- The `n`th transverse wave number for ideal parallel plates separated by `a`.
The physical mode index is usually `n >= 1`; Lean keeps `n : ℕ` and downstream
statements can impose `0 < n` when needed. -/
noncomputable def transverseWaveNumber (a : PlateSeparation) (n : ℕ) : ℝ :=
  (n : ℝ) * Real.pi / a.value

/-- Photon frequency for a transverse mode in the one-dimensional scalar toy
model.  This is the part of the full electromagnetic spectrum that carries the
`1/a` scaling. -/
noncomputable def modeFrequency (a : PlateSeparation) (n : ℕ) : ℝ :=
  c * transverseWaveNumber a n

/-- Zero-point energy for a single mode, `E_0 = ℏω/2`. -/
noncomputable def zeroPointModeEnergy (ω : ℝ) : ℝ :=
  hbar * ω / 2

/-- The positive coefficient `K = π² ℏ c / 720` in the ideal parallel-plate
energy density `E/A = -K/a³`. -/
noncomputable def idealEnergyCoefficient : ℝ :=
  Real.pi ^ 2 * hbar * c / 720

/-- Ideal renormalized Casimir energy per unit area for parallel conducting
plates.  The analytic input is the regularized mode-sum law. -/
noncomputable def idealEnergyDensity (a : PlateSeparation) : ℝ :=
  -idealEnergyCoefficient / a.value ^ 3

/-- The derivative of `idealEnergyDensity` with respect to the plate separation,
given by the elementary derivative of `-K a^{-3}`. -/
noncomputable def idealEnergyDerivative (a : PlateSeparation) : ℝ :=
  3 * idealEnergyCoefficient / a.value ^ 4

/-- Ideal attractive Casimir pressure between parallel conducting plates. -/
noncomputable def idealPressure (a : PlateSeparation) : ℝ :=
  -Real.pi ^ 2 * hbar * c / (240 * a.value ^ 4)

/-- The ideal energy coefficient is positive. -/
theorem idealEnergyCoefficient_pos : 0 < idealEnergyCoefficient := by
  unfold idealEnergyCoefficient
  apply div_pos
  · exact mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) hbar_pos) c_pos
  · norm_num

/-- The elementary energy derivative is positive for positive separation. -/
theorem idealEnergyDerivative_pos (a : PlateSeparation) :
    0 < idealEnergyDerivative a := by
  unfold idealEnergyDerivative
  apply div_pos
  · exact mul_pos (by norm_num) idealEnergyCoefficient_pos
  · exact pow_pos a.pos 4

/-- Pressure is minus the derivative of the ideal renormalized energy density. -/
theorem idealPressure_eq_neg_energyDerivative (a : PlateSeparation) :
    idealPressure a = -idealEnergyDerivative a := by
  unfold idealPressure idealEnergyDerivative idealEnergyCoefficient
  ring

/-- The ideal Casimir pressure is attractive. -/
theorem idealPressure_negative (a : PlateSeparation) :
    idealPressure a < 0 := by
  rw [idealPressure_eq_neg_energyDerivative]
  exact neg_neg_of_pos (idealEnergyDerivative_pos a)

/-- Magnitude form of the ideal pressure. -/
theorem neg_idealPressure_eq_derivative (a : PlateSeparation) :
    -idealPressure a = idealEnergyDerivative a := by
  rw [idealPressure_eq_neg_energyDerivative]
  ring

/-- The characteristic `a^{-4}` pressure scaling: multiplying by `a^4` removes
the separation dependence. -/
theorem idealPressure_fourth_power_scaling (a : PlateSeparation) :
    a.value ^ 4 * (-idealPressure a) = Real.pi ^ 2 * hbar * c / 240 := by
  rw [neg_idealPressure_eq_derivative]
  unfold idealEnergyDerivative idealEnergyCoefficient
  have ha : a.value ≠ 0 := ne_of_gt a.pos
  have ha4 : a.value ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt a.pos)
  field_simp [ha4, ha]
  ring_nf

/-- RS-native substitution of Planck's constant in the ideal pressure law. -/
theorem idealPressure_hbar_phi_form (a : PlateSeparation) :
    idealPressure a =
      -Real.pi ^ 2 * (phi ^ (-(5 : ℝ))) * c / (240 * a.value ^ 4) := by
  unfold idealPressure
  rw [hbar_eq_phi_inv_fifth]

/-- The ideal pressure law has no zero at finite positive separation. -/
theorem idealPressure_ne_zero (a : PlateSeparation) :
    idealPressure a ≠ 0 := by
  exact ne_of_lt (idealPressure_negative a)

/-- A compact certificate for the ideal parallel-plate core. -/
structure IdealPlateCert where
  coefficient_pos : 0 < idealEnergyCoefficient
  pressure_from_energy :
    ∀ a : PlateSeparation, idealPressure a = -idealEnergyDerivative a
  attractive : ∀ a : PlateSeparation, idealPressure a < 0
  fourth_power_scaling :
    ∀ a : PlateSeparation,
      a.value ^ 4 * (-idealPressure a) = Real.pi ^ 2 * hbar * c / 240
  hbar_phi_form :
    ∀ a : PlateSeparation,
      idealPressure a =
        -Real.pi ^ 2 * (phi ^ (-(5 : ℝ))) * c / (240 * a.value ^ 4)

/-- The ideal parallel-plate Casimir certificate. -/
def idealPlateCert : IdealPlateCert where
  coefficient_pos := idealEnergyCoefficient_pos
  pressure_from_energy := idealPressure_eq_neg_energyDerivative
  attractive := idealPressure_negative
  fourth_power_scaling := idealPressure_fourth_power_scaling
  hbar_phi_form := idealPressure_hbar_phi_form

end

end CasimirPlateModes
end QFT
end IndisputableMonolith

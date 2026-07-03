import Mathlib
import IndisputableMonolith.QFT.CasimirZetaRegularization

/-!
# Proximity Force Approximation

Sphere-plate Casimir measurements are usually interpreted through the
proximity force approximation: the sphere-plate force is `2πR` times the
parallel-plate energy density at the closest separation.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirPFA

open CasimirPlateModes
open Constants

noncomputable section

/-- Proximity-force approximation for a sphere of radius `R` above a plate. -/
noncomputable def pfaForce (R : ℝ) (a : PlateSeparation) : ℝ :=
  2 * Real.pi * R * idealEnergyDensity a

/-- PFA force is attractive for positive radius and positive separation. -/
theorem pfaForce_attractive_of_R_pos
    (R : ℝ) (a : PlateSeparation) (hR : 0 < R) :
    pfaForce R a < 0 := by
  unfold pfaForce idealEnergyDensity
  have hcoef : 0 < idealEnergyCoefficient := idealEnergyCoefficient_pos
  have henergy : -idealEnergyCoefficient / a.value ^ 3 < 0 := by
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hcoef) (pow_pos a.pos 3)
  exact mul_neg_of_pos_of_neg (mul_pos (mul_pos (by norm_num) Real.pi_pos) hR) henergy

/-- PFA has cubic separation scaling. -/
theorem pfaForce_cubic_scaling
    (R : ℝ) (a : PlateSeparation) :
    a.value ^ 3 * (-pfaForce R a) =
      R * (Real.pi ^ 3 * hbar * c) / 360 := by
  unfold pfaForce idealEnergyDensity idealEnergyCoefficient
  have ha : a.value ≠ 0 := ne_of_gt a.pos
  have ha3 : a.value ^ 3 ≠ 0 := pow_ne_zero 3 ha
  field_simp [ha, ha3]
  ring

/-- Sphere-plate PFA certificate. -/
structure SpherePlateCert where
  attractive :
    ∀ (R : ℝ) (a : PlateSeparation), 0 < R → pfaForce R a < 0
  cubic_scaling :
    ∀ (R : ℝ) (a : PlateSeparation),
      a.value ^ 3 * (-pfaForce R a) =
        R * (Real.pi ^ 3 * hbar * c) / 360
  zeta_backed_energy :
    ∀ a : PlateSeparation,
      idealEnergyDensity a =
        CasimirZetaRegularization.regularizedModeSum a

/-- Certificate instance for sphere-plate PFA. -/
def spherePlateCert : SpherePlateCert where
  attractive := pfaForce_attractive_of_R_pos
  cubic_scaling := pfaForce_cubic_scaling
  zeta_backed_energy := CasimirZetaRegularization.idealEnergyDensity_from_zeta

end

end CasimirPFA
end QFT
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Casimir Torque

Anisotropic boundaries produce a torque from angularly dependent mode
admissibility.  This module formalizes the standard sinusoidal structural law.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirTorque

open CasimirPlateModes

noncomputable section

/-- Structural anisotropic Casimir torque law. -/
noncomputable def casimirTorque (beta : ℝ) (a : PlateSeparation) (theta : ℝ) : ℝ :=
  beta * idealEnergyDensity a * Real.sin (2 * theta)

/-- Aligned anisotropic plates have zero torque. -/
theorem torque_zero_at_aligned (beta : ℝ) (a : PlateSeparation) :
    casimirTorque beta a 0 = 0 := by
  unfold casimirTorque
  simp

/-- Orthogonal alignment also has zero torque in the `sin(2θ)` structural law. -/
theorem torque_zero_at_orthogonal (beta : ℝ) (a : PlateSeparation) :
    casimirTorque beta a (Real.pi / 2) = 0 := by
  unfold casimirTorque
  rw [show 2 * (Real.pi / 2) = Real.pi by ring]
  simp

/-- Quarter-turn alignment evaluates to the full anisotropic amplitude. -/
theorem torque_at_quarter_turn (beta : ℝ) (a : PlateSeparation) :
    casimirTorque beta a (Real.pi / 4) = beta * idealEnergyDensity a := by
  unfold casimirTorque
  rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring]
  rw [Real.sin_pi_div_two]
  ring

/-- Torque certificate. -/
structure CasimirTorqueCert where
  aligned_zero : ∀ beta a, casimirTorque beta a 0 = 0
  orthogonal_zero : ∀ beta a, casimirTorque beta a (Real.pi / 2) = 0
  quarter_turn_value :
    ∀ beta a, casimirTorque beta a (Real.pi / 4) = beta * idealEnergyDensity a

/-- Certificate instance. -/
def casimirTorqueCert : CasimirTorqueCert where
  aligned_zero := torque_zero_at_aligned
  orthogonal_zero := torque_zero_at_orthogonal
  quarter_turn_value := torque_at_quarter_turn

end

end CasimirTorque
end QFT
end IndisputableMonolith

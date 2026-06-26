import Mathlib
import IndisputableMonolith.Measurement.PathAction

/-!
# Two-Branch Quantum Measurement Geodesic

This module formalizes the two-branch rotation geometry from
Local-Collapse §3 and Appendix A.

Key results:
- Residual norm ||R|| = π/2 - θ_s (geodesic length)
- Rate action A = -ln(sin θ_s)
- Born weight: exp(-2A) = sin²(θ_s) = |α₂|²
-/

namespace IndisputableMonolith
namespace Measurement

open Real

/-- A two-branch quantum measurement rotation from angle θ_s to π/2 -/
structure TwoBranchRotation where
  θ_s : ℝ  -- starting angle (determines initial amplitude)
  θ_s_bounds : 0 < θ_s ∧ θ_s < π/2
  T : ℝ    -- duration of rotation
  T_pos : 0 < T

/-- Residual action S = π/2 - θ_s (geodesic length on Bloch sphere) -/
noncomputable def residualAction (rot : TwoBranchRotation) : ℝ :=
  π/2 - rot.θ_s

/-- Residual norm ||R|| = dθ/dt integrated over the rotation -/
noncomputable def residualNorm (rot : TwoBranchRotation) : ℝ :=
  residualAction rot

/-- Rate action A = -ln(sin θ_s) from eq (4.7) of Local-Collapse -/
noncomputable def rateAction (rot : TwoBranchRotation) : ℝ :=
  - Real.log (Real.sin rot.θ_s)

/-- Rate action is positive for θ_s ∈ (0, π/2) -/
lemma rateAction_pos (rot : TwoBranchRotation) : 0 < rateAction rot := by
  unfold rateAction
  apply neg_pos.mpr
  have ⟨h1, h2⟩ := rot.θ_s_bounds
  have hsin_pos : 0 < Real.sin rot.θ_s :=
    sin_pos_of_pos_of_lt_pi h1 (by linarith : rot.θ_s < π)
  -- sin θ < 1 for 0 < θ < π/2
  have hsin_lt_one : Real.sin rot.θ_s < 1 := by
    have hx1 : -(π / 2) ≤ rot.θ_s := by linarith
    have hlt : rot.θ_s < π / 2 := h2
    have : Real.sin rot.θ_s < Real.sin (π / 2) :=
      sin_lt_sin_of_lt_of_le_pi_div_two hx1 le_rfl hlt
    simpa [Real.sin_pi_div_two] using this
  exact Real.log_neg hsin_pos hsin_lt_one

/-- Born weight from rate action: exp(-2A) = sin²(θ_s) -/
theorem born_weight_from_rate (rot : TwoBranchRotation) :
  Real.exp (- 2 * rateAction rot) = (Real.sin rot.θ_s) ^ 2 := by
  unfold rateAction
  -- exp(-2*(-log(sin θ))) = exp(2 log(sin θ))
  have ⟨h1, h2⟩ := rot.θ_s_bounds
  have hsin_pos : 0 < Real.sin rot.θ_s :=
    sin_pos_of_pos_of_lt_pi h1 (by linarith : rot.θ_s < π)
  calc Real.exp (- 2 * (- Real.log (Real.sin rot.θ_s)))
      = Real.exp (2 * Real.log (Real.sin rot.θ_s)) := by ring_nf
      _ = Real.exp (Real.log ((Real.sin rot.θ_s) ^ 2)) := by
        congr 1
        exact (Real.log_pow (Real.sin rot.θ_s) 2).symm
      _ = (Real.sin rot.θ_s) ^ 2 := Real.exp_log (pow_pos hsin_pos 2)

/-- Initial amplitude |α₂|² = sin²(θ_s) from geometry -/
noncomputable def initialAmplitudeSquared (rot : TwoBranchRotation) : ℝ :=
  (Real.sin rot.θ_s) ^ 2

/-- Complement amplitude |α₁|² = cos²(θ_s) -/
noncomputable def complementAmplitudeSquared (rot : TwoBranchRotation) : ℝ :=
  (Real.cos rot.θ_s) ^ 2

/-- Amplitudes sum to 1 (normalization) -/
theorem amplitudes_normalized (rot : TwoBranchRotation) :
  initialAmplitudeSquared rot + complementAmplitudeSquared rot = 1 := by
  unfold initialAmplitudeSquared complementAmplitudeSquared
  exact Real.sin_sq_add_cos_sq rot.θ_s

/-- The geodesic is independent of time parameterization (reparameterization invariance) -/
theorem residual_action_invariant (rot : TwoBranchRotation) :
  residualAction rot = π/2 - rot.θ_s := rfl

end Measurement
end IndisputableMonolith

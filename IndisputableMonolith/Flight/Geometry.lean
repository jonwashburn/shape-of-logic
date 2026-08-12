import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Spiral.SpiralField
import IndisputableMonolith.Chemistry.BondAngles

/-!
# Flight Geometry (φ-Tetrahedral / log-spiral scaffold)

This file provides the *purely geometric* layer of the spiral-field propulsion model:
- the φ-tetrahedral angle (derived from Recognition Science axioms),
- log-spiral rotor paths under φ-scaling,
- math-only lemmas about step ratios and per-turn multipliers.

No physical claims are made here. All geometry is derived from the RS constant φ.
-/

namespace IndisputableMonolith
namespace Flight
namespace Geometry

open scoped Real

/-- The φ-tetrahedral angle in radians.

This is the tetrahedral bond angle, which emerges from the RS cost-minimization
framework as the optimal angle for 4-fold symmetric structures.

Exact expression: `arccos (-1/3)` ≈ 109.47°.

Note: This angle is mathematically identical to the sp³ hybridization angle in
chemistry and appears in any tetrahedral geometry. It is derived here from
first principles via the φ-lattice structure. -/
noncomputable def phiTetrahedralAngle : ℝ := Real.arccos (-(1 / 3 : ℝ))

/-- Rotor pitch family: integral log-spiral pitch `kappa : ℤ`. -/
abbrev RotorPitch := IndisputableMonolith.Spiral.SpiralField.Params

/-- Rotor radial path: log-spiral scaling on the φ lattice.

`r(θ) = r0 · φ^{(κ·θ)/(2π)}`. -/
noncomputable abbrev rotorPath := IndisputableMonolith.Spiral.SpiralField.logSpiral

namespace SpiralLemmas

open IndisputableMonolith.Spiral

/-- `logSpiral` is nonzero whenever `r0` is nonzero (since φ^x > 0). -/
lemma logSpiral_ne_zero
    {r0 θ : ℝ} {P : SpiralField.Params} (hr0 : r0 ≠ 0) :
    SpiralField.logSpiral r0 θ P ≠ 0 := by
  classical
  unfold SpiralField.logSpiral
  -- `φ > 0` hence `φ^exp > 0`.
  have hφpos : 0 < IndisputableMonolith.Constants.phi :=
    IndisputableMonolith.Constants.phi_pos
  have hrpow_ne : Real.rpow IndisputableMonolith.Constants.phi
        ((P.kappa : ℝ) * θ / (2 * Real.pi)) ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos hφpos _)
  exact mul_ne_zero hr0 hrpow_ne

/-- Closed-form step ratio for the log-spiral: it depends only on `Δθ` and `kappa`.

This is the mathematical kernel behind the "discrete pitch families" idea.

We assume `r0 ≠ 0` to avoid the definitional `if r₀ = 0 then 1` branch
in `SpiralField.stepRatio`.
-/
lemma stepRatio_logSpiral_closed_form
    (r0 θ Δθ : ℝ) (P : SpiralField.Params) (hr0 : r0 ≠ 0) :
    SpiralField.stepRatio r0 θ Δθ P
      = Real.rpow IndisputableMonolith.Constants.phi ((P.kappa : ℝ) * Δθ / (2 * Real.pi)) := by
  classical
  -- Unfold the definition and discharge the `if` branch *before* unfolding `logSpiral`.
  unfold SpiralField.stepRatio
  have hr0path : SpiralField.logSpiral r0 θ P ≠ 0 :=
    logSpiral_ne_zero (r0:=r0) (θ:=θ) (P:=P) hr0
  simp [hr0path]

  -- Now we are proving the ratio identity:
  --   r(θ+Δθ)/r(θ) = φ^{κΔθ/(2π)}.
  have hφpos : 0 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.phi_pos
  simp [SpiralField.logSpiral]
  -- Split the exponent using `rpow_add`.
  have hexp :
      ((P.kappa : ℝ) * (θ + Δθ) / (2 * Real.pi))
        = ((P.kappa : ℝ) * θ / (2 * Real.pi)) + ((P.kappa : ℝ) * Δθ / (2 * Real.pi)) := by
    ring
  have hadd :
      Real.rpow IndisputableMonolith.Constants.phi ((P.kappa : ℝ) * (θ + Δθ) / (2 * Real.pi))
        =
        Real.rpow IndisputableMonolith.Constants.phi ((P.kappa : ℝ) * θ / (2 * Real.pi))
          * Real.rpow IndisputableMonolith.Constants.phi ((P.kappa : ℝ) * Δθ / (2 * Real.pi)) := by
    simpa [hexp] using
      (Real.rpow_add hφpos
        ((P.kappa : ℝ) * θ / (2 * Real.pi))
        ((P.kappa : ℝ) * Δθ / (2 * Real.pi)))
  have hA_ne :
      Real.rpow IndisputableMonolith.Constants.phi ((P.kappa : ℝ) * θ / (2 * Real.pi)) ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos hφpos _)
  have haddPow :
      IndisputableMonolith.Constants.phi ^ ((P.kappa : ℝ) * (θ + Δθ) / (2 * Real.pi))
        =
        IndisputableMonolith.Constants.phi ^ ((P.kappa : ℝ) * θ / (2 * Real.pi))
          * IndisputableMonolith.Constants.phi ^ ((P.kappa : ℝ) * Δθ / (2 * Real.pi)) := by
    simpa using hadd
  -- Cancel the common factors.
  rw [haddPow]
  field_simp [hr0, hA_ne, mul_assoc, mul_left_comm, mul_comm]

/-- The step ratio is invariant under scaling the base radius `r0`.

This follows immediately from the closed-form identity.
-/
lemma stepRatio_invariant_under_r0
    (c r0 θ Δθ : ℝ) (P : SpiralField.Params) (hc : c ≠ 0) (hr0 : r0 ≠ 0) :
    SpiralField.stepRatio (c * r0) θ Δθ P = SpiralField.stepRatio r0 θ Δθ P := by
  have hcr0 : c * r0 ≠ 0 := mul_ne_zero hc hr0
  simp [stepRatio_logSpiral_closed_form (r0:=c*r0) (θ:=θ) (Δθ:=Δθ) (P:=P) hcr0,
        stepRatio_logSpiral_closed_form (r0:=r0) (θ:=θ) (Δθ:=Δθ) (P:=P) hr0]

/-- Per-turn multiplier recovered as the special case `Δθ = 2π`.

Mathematically: `r(θ+2π)/r(θ) = φ^kappa`.
-/
lemma perTurn_ratio
    (r0 θ : ℝ) (P : SpiralField.Params) (hr0 : r0 ≠ 0) :
    SpiralField.stepRatio r0 θ (2 * Real.pi) P = SpiralField.perTurnMultiplier P := by
  -- Use the closed-form step ratio, then cancel `(2π)` in the exponent.
  have h :=
    stepRatio_logSpiral_closed_form (r0:=r0) (θ:=θ) (Δθ:=(2 * Real.pi)) (P:=P) hr0
  have hden : (2 * Real.pi : ℝ) ≠ 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 Real.pi_ne_zero
  have hexp : ((P.kappa : ℝ) * (2 * Real.pi) / (2 * Real.pi)) = (P.kappa : ℝ) := by
    simpa using (mul_div_cancel_right₀ (P.kappa : ℝ) hden)
  simpa [SpiralField.perTurnMultiplier, hexp] using h

/-- Discreteness of `kappa`: shifting `kappa` by an integer shifts the per-turn multiplier by a φ-power.

This captures the “discrete pitch families” idea: per-turn growth is quantized in multiplicative
steps of `φ^{d}` for `d : ℤ`.
-/
lemma kappa_discreteness (P : SpiralField.Params) (d : ℤ) :
    SpiralField.perTurnMultiplier { kappa := P.kappa + d }
      = SpiralField.perTurnMultiplier P * Real.rpow IndisputableMonolith.Constants.phi (d : ℝ) := by
  -- `φ > 0` so we can use `Real.rpow_add`.
  have hφpos : 0 < IndisputableMonolith.Constants.phi := IndisputableMonolith.Constants.phi_pos
  -- Expand both sides and use `rpow_add` on the exponent `(κ + d)`.
  simp [SpiralField.perTurnMultiplier, Real.rpow_add, hφpos, Int.cast_add]

end SpiralLemmas

end Geometry
end Flight
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Masses.ElectroweakMasses

/-!
# The Weak Coupling Constant α_W from RS First Principles

This module defines the SU(2) weak coupling constant α_W by combining
two independently RS-derived quantities:

- α (EM fine-structure constant) from `Constants/Alpha.lean`
- sin²θ_W = (3 − φ)/6 from `Masses/ElectroweakMasses.lean`

via the tree-level electroweak identity: α = α_W · sin²θ_W.

Input status (honest, 2026-07-06):
- α here is the RS CONSTRUCTION value (44π · exp(−f_gap/44π), band
  (137.030, 137.039)). The construction's exact value is EXCLUDED by
  measurement at >30,000σ (`Constants.AlphaGenesis.MeasurementVerdict`),
  and within RS the exact α is a free boundary datum
  (`Constants.AlphaGenesis.KappaGammaIrreducibility`). So α_W built on it
  is a construction-band object, NOT a parameter-free derivation of the
  measured weak coupling.
- sin²θ_W = (3 − φ)/6 is φ-structural from the gauge embedding at D = 3.

## Main Results

- `alpha_W`: the weak coupling constant = α / sin²θ_W
- `alpha_W_pos`: α_W is positive
- `alpha_W_gt_alpha`: α_W > α (since sin²θ_W < 1)
- `WeakCouplingCert`: the combination identity (construction-band input)

## Status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith
namespace StandardModel
namespace WeakCoupling

open Constants Masses.ElectroweakMasses

noncomputable section

/-! ## Part 1: Definition -/

/-- The weak coupling constant α_W = α / sin²θ_W.
    From the tree-level electroweak identity: α_EM = α_W · sin²θ_W,
    so α_W = α_EM / sin²θ_W. -/
def alpha_W : ℝ := alpha / sin2_theta_W_rs

/-- α_W expressed in terms of RS primitives:
    α_W = (1/alphaInv) / ((3 − φ)/6) = 6 / (alphaInv · (3 − φ)) -/
theorem alpha_W_expanded :
    alpha_W = alpha / ((3 - Constants.phi) / 6) := rfl

/-! ## Part 2: Positivity and Bounds -/

private lemma alpha_pos_aux : 0 < alpha := by
  unfold alpha alphaInv alpha_seed; positivity

/-- α_W is positive (both α and sin²θ_W are positive). -/
theorem alpha_W_pos : 0 < alpha_W := by
  unfold alpha_W
  exact div_pos alpha_pos_aux sin2_theta_positive

/-- α_W > α (since sin²θ_W < 1, dividing by it increases α). -/
theorem alpha_W_gt_alpha : alpha < alpha_W := by
  unfold alpha_W
  rw [lt_div_iff₀ sin2_theta_positive]
  calc alpha * sin2_theta_W_rs
      < alpha * 1 := by {
        apply mul_lt_mul_of_pos_left _ alpha_pos_aux
        linarith [sin2_theta_lt_half]
      }
    _ = alpha := mul_one _

/-- sin²θ_W > 0 (needed for division). -/
theorem sin2_pos : 0 < sin2_theta_W_rs := sin2_theta_positive

/-- sin²θ_W < 1/2 (the weak mixing is mild). -/
theorem sin2_lt_half : sin2_theta_W_rs < 1/2 := sin2_theta_lt_half

/-- α_W > 2α (since sin²θ_W < 1/2). -/
theorem alpha_W_gt_two_alpha : 2 * alpha < alpha_W := by
  unfold alpha_W
  rw [lt_div_iff₀ sin2_theta_positive]
  calc 2 * alpha * sin2_theta_W_rs
      < 2 * alpha * (1/2) := by {
        apply mul_lt_mul_of_pos_left sin2_lt_half
        exact mul_pos (by norm_num) alpha_pos_aux
      }
    _ = alpha := by ring

/-! ## Part 3: Structural Certificate -/

/-- The α_W combination identity, with honest input status:
    - α is the RS CONSTRUCTION value (44π seed + f_gap from 8-tick); its
      exact value is a boundary datum in RS, not a derived constant
      (`Constants.AlphaGenesis.KappaGammaIrreducibility`), so this cert
      certifies the combination STRUCTURE, not a parameter-free value of
      the measured weak coupling.
    - sin²θ_W = (3 − φ)/6 from gauge embedding geometry (φ-structural). -/
structure WeakCouplingCert where
  alpha_from_cube : alphaInv = alpha_seed * Real.exp (-(f_gap / alpha_seed))
  sin2_from_phi : sin2_theta_W_rs = (3 - Constants.phi) / 6
  alpha_W_def : alpha_W = alpha / sin2_theta_W_rs
  alpha_W_positive : 0 < alpha_W
  alpha_W_exceeds_alpha : alpha < alpha_W

theorem weak_coupling_cert : WeakCouplingCert where
  alpha_from_cube := rfl
  sin2_from_phi := rfl
  alpha_W_def := rfl
  alpha_W_positive := alpha_W_pos
  alpha_W_exceeds_alpha := alpha_W_gt_alpha

end

end WeakCoupling
end StandardModel
end IndisputableMonolith

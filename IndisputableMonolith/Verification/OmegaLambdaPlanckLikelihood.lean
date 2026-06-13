import Mathlib
import IndisputableMonolith.Cosmology.OmegaLambdaDerivation
import IndisputableMonolith.Verification.FalsifierRegisterDatasets

/-!
# ΩΛ Planck Likelihood Attachment

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module upgrades the §7 ΩΛ falsifier-register row from a dataset
attachment to a dataset-specific likelihood-style Lean certificate.

The underlying prediction comes from
`Cosmology.OmegaLambdaDerivation`:

* `omega_lambda = 11/16 - α/π`
* `0.683 < omega_lambda ∧ omega_lambda < 0.686`
* `|omega_lambda - omega_lambda_planck2018| < 2 * omega_lambda_planck_err`

The dataset record comes from
`Verification.FalsifierRegisterDatasets.omegaLambdaAttachment`:

* Planck 2018 TT,TE,EE+lowE+lensing
* `ΩΛ = 0.6889 ± 0.0056`
* currently sensitive to the RS interval at the two-sigma consistency level

This is a consistency test, not empirical confirmation.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace OmegaLambdaPlanckLikelihood

open IndisputableMonolith.Cosmology.OmegaLambdaDerivation
open IndisputableMonolith.Verification.FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset constants and residual -/

/-- Planck 2018 central value for ΩΛ. -/
def planckOmegaLambdaCentral : ℝ := omega_lambda_planck2018

/-- Planck 2018 one-sigma uncertainty for ΩΛ. -/
def planckOmegaLambdaSigma : ℝ := omega_lambda_planck_err

/-- Absolute residual between the RS prediction and the Planck 2018 central value. -/
def omegaLambdaPlanckResidual : ℝ :=
  |omega_lambda - planckOmegaLambdaCentral|

/-- Two-sigma Planck tolerance. -/
def planckOmegaLambdaTwoSigma : ℝ :=
  2 * planckOmegaLambdaSigma

theorem planckOmegaLambdaSigma_pos : 0 < planckOmegaLambdaSigma := by
  unfold planckOmegaLambdaSigma omega_lambda_planck_err
  norm_num

theorem planckOmegaLambdaTwoSigma_pos : 0 < planckOmegaLambdaTwoSigma := by
  unfold planckOmegaLambdaTwoSigma
  exact mul_pos (by norm_num) planckOmegaLambdaSigma_pos

/-! ## §2. Lean likelihood-style consistency certificate -/

/-- RS ΩΛ lies within Planck 2018's two-sigma band. -/
theorem omegaLambda_residual_lt_two_sigma :
    omegaLambdaPlanckResidual < planckOmegaLambdaTwoSigma := by
  unfold omegaLambdaPlanckResidual planckOmegaLambdaTwoSigma planckOmegaLambdaCentral
    planckOmegaLambdaSigma
  exact rs_consistent_with_planck

/-- Interval form of the same two-sigma consistency statement. -/
theorem omegaLambda_in_planck_two_sigma_interval :
    planckOmegaLambdaCentral - planckOmegaLambdaTwoSigma < omega_lambda ∧
      omega_lambda < planckOmegaLambdaCentral + planckOmegaLambdaTwoSigma := by
  have h := omegaLambda_residual_lt_two_sigma
  unfold omegaLambdaPlanckResidual at h
  rw [abs_lt] at h
  unfold planckOmegaLambdaCentral planckOmegaLambdaTwoSigma planckOmegaLambdaSigma at h ⊢
  constructor <;> linarith

/-- The Planck dataset attachment row is positive-sensitivity and currently sensitive. -/
theorem omegaLambda_dataset_attachment_active :
    HasPositiveSensitivity omegaLambdaAttachment ∧
    HasPositiveTargetScale omegaLambdaAttachment ∧
    omegaLambdaAttachment.currentlySensitive = true :=
  ⟨omegaLambda_sensitivity_pos, omegaLambda_target_pos, rfl⟩

/-! ## §3. Master cert -/

structure OmegaLambdaPlanckLikelihoodCert where
  sigma_pos : 0 < planckOmegaLambdaSigma
  two_sigma_pos : 0 < planckOmegaLambdaTwoSigma
  residual_lt_two_sigma :
    omegaLambdaPlanckResidual < planckOmegaLambdaTwoSigma
  interval_form :
    planckOmegaLambdaCentral - planckOmegaLambdaTwoSigma < omega_lambda ∧
      omega_lambda < planckOmegaLambdaCentral + planckOmegaLambdaTwoSigma
  dataset_active :
    HasPositiveSensitivity omegaLambdaAttachment ∧
    HasPositiveTargetScale omegaLambdaAttachment ∧
    omegaLambdaAttachment.currentlySensitive = true

def omegaLambdaPlanckLikelihoodCert : OmegaLambdaPlanckLikelihoodCert where
  sigma_pos := planckOmegaLambdaSigma_pos
  two_sigma_pos := planckOmegaLambdaTwoSigma_pos
  residual_lt_two_sigma := omegaLambda_residual_lt_two_sigma
  interval_form := omegaLambda_in_planck_two_sigma_interval
  dataset_active := omegaLambda_dataset_attachment_active

theorem omegaLambdaPlanckLikelihoodCert_inhabited :
    Nonempty OmegaLambdaPlanckLikelihoodCert :=
  ⟨omegaLambdaPlanckLikelihoodCert⟩

/-- One-statement ΩΛ likelihood attachment theorem. -/
theorem omega_lambda_planck_likelihood_one_statement :
    (omegaLambdaPlanckResidual < planckOmegaLambdaTwoSigma) ∧
    (planckOmegaLambdaCentral - planckOmegaLambdaTwoSigma < omega_lambda ∧
      omega_lambda < planckOmegaLambdaCentral + planckOmegaLambdaTwoSigma) ∧
    (omegaLambdaAttachment.currentlySensitive = true) ∧
    Nonempty OmegaLambdaPlanckLikelihoodCert :=
  ⟨omegaLambda_residual_lt_two_sigma,
   omegaLambda_in_planck_two_sigma_interval,
   rfl,
   omegaLambdaPlanckLikelihoodCert_inhabited⟩

end

end OmegaLambdaPlanckLikelihood
end Verification
end IndisputableMonolith

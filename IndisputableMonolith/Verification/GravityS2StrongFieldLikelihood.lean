import Mathlib
import IndisputableMonolith.Gravity.StrongFieldStructural
import IndisputableMonolith.Verification.FalsifierRegisterDatasets

/-!
# GRAVITY S2 Strong-Field Likelihood Attachment

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module upgrades the §7 strong-field falsifier row with a second
dataset-specific likelihood-style certificate, this time for the GRAVITY
Collaboration's S2 Schwarzschild-precession measurement.

Dataset:

* GRAVITY Collaboration (2020) S2 precession:
  `f_SP = 1.10 ± 0.19`, where `f_SP = 0` is Newtonian and `f_SP = 1`
  is GR.

RS structural target:

* a tiny positive deviation from GR, represented structurally as
  `f_SP = 1 + φ⁻⁴⁴`.

The certificate proves two honest facts:

1. GRAVITY's central value is statistically compatible with the RS
   structural target at 1σ.
2. GRAVITY is **not currently sensitive** to the RS target scale:
   `φ⁻⁴⁴` is far below the reported `0.19` one-sigma precision.

This is a consistency / non-sensitivity test, not empirical confirmation.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GravityS2StrongFieldLikelihood

open IndisputableMonolith.Verification.FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset constants and residual -/

/-- GRAVITY S2 central measurement for the Schwarzschild-precession factor. -/
def gravityS2FSPCentral : ℝ := 1.10

/-- GRAVITY S2 one-sigma uncertainty for `f_SP`. -/
def gravityS2FSPSigma : ℝ := 0.19

/-- RS structural target deviation scale, taken from the §7 strong-field attachment. -/
def gravityS2RSTargetScale : ℝ := strongFieldAttachment.rsTargetScale

/-- RS structural target for the S2 precession factor: GR value plus φ⁻⁴⁴. -/
def gravityS2RSPredictedFSP : ℝ := 1 + gravityS2RSTargetScale

/-- Residual between GRAVITY S2 central value and the RS structural target. -/
def gravityS2Residual : ℝ :=
  |gravityS2FSPCentral - gravityS2RSPredictedFSP|

theorem gravityS2FSPSigma_pos : 0 < gravityS2FSPSigma := by
  unfold gravityS2FSPSigma
  norm_num

theorem gravityS2RSTargetScale_pos : 0 < gravityS2RSTargetScale := by
  unfold gravityS2RSTargetScale strongFieldAttachment
  norm_num

/-! ## §2. Likelihood-style statements -/

/-- GRAVITY S2 central value is within 1σ of the RS structural target. -/
theorem gravityS2_residual_lt_one_sigma :
    gravityS2Residual < gravityS2FSPSigma := by
  unfold gravityS2Residual gravityS2FSPCentral gravityS2RSPredictedFSP
    gravityS2RSTargetScale gravityS2FSPSigma strongFieldAttachment
  norm_num

/-- GRAVITY S2 is not currently sensitive to the φ⁻⁴⁴ target:
the one-sigma uncertainty is larger than the target scale. -/
theorem gravityS2_sigma_gt_rs_target :
    gravityS2RSTargetScale < gravityS2FSPSigma := by
  unfold gravityS2RSTargetScale gravityS2FSPSigma strongFieldAttachment
  norm_num

/-- Strong-field dataset attachment is present, positive, and explicitly
marked not currently sensitive. -/
theorem gravityS2_dataset_attachment_status :
    HasPositiveSensitivity strongFieldAttachment ∧
    HasPositiveTargetScale strongFieldAttachment ∧
    strongFieldAttachment.currentlySensitive = false :=
  ⟨strongField_sensitivity_pos, strongField_target_pos, rfl⟩

/-! ## §3. Master cert -/

structure GravityS2StrongFieldLikelihoodCert where
  sigma_pos : 0 < gravityS2FSPSigma
  target_pos : 0 < gravityS2RSTargetScale
  residual_lt_one_sigma :
    gravityS2Residual < gravityS2FSPSigma
  not_currently_sensitive :
    gravityS2RSTargetScale < gravityS2FSPSigma
  dataset_status :
    HasPositiveSensitivity strongFieldAttachment ∧
    HasPositiveTargetScale strongFieldAttachment ∧
    strongFieldAttachment.currentlySensitive = false

def gravityS2StrongFieldLikelihoodCert : GravityS2StrongFieldLikelihoodCert where
  sigma_pos := gravityS2FSPSigma_pos
  target_pos := gravityS2RSTargetScale_pos
  residual_lt_one_sigma := gravityS2_residual_lt_one_sigma
  not_currently_sensitive := gravityS2_sigma_gt_rs_target
  dataset_status := gravityS2_dataset_attachment_status

theorem gravityS2StrongFieldLikelihoodCert_inhabited :
    Nonempty GravityS2StrongFieldLikelihoodCert :=
  ⟨gravityS2StrongFieldLikelihoodCert⟩

/-- One-statement GRAVITY S2 likelihood attachment theorem. -/
theorem gravity_s2_strong_field_likelihood_one_statement :
    (gravityS2Residual < gravityS2FSPSigma) ∧
    (gravityS2RSTargetScale < gravityS2FSPSigma) ∧
    (strongFieldAttachment.currentlySensitive = false) ∧
    Nonempty GravityS2StrongFieldLikelihoodCert :=
  ⟨gravityS2_residual_lt_one_sigma,
   gravityS2_sigma_gt_rs_target,
   rfl,
   gravityS2StrongFieldLikelihoodCert_inhabited⟩

end

end GravityS2StrongFieldLikelihood
end Verification
end IndisputableMonolith

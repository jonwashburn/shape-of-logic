import Mathlib
import IndisputableMonolith.Gravity.StrongFieldStructural
import IndisputableMonolith.Verification.FalsifierRegisterDatasets

/-!
# EHT M87* Strong-Field Likelihood Attachment

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module upgrades the §7 strong-field falsifier row with a third
dataset-specific likelihood-style certificate, this time for Event
Horizon Telescope observations of M87*.

Dataset:

* EHT M87* first image:
  ring diameter `42 ± 3 μas`, circularity deviation ≤10%, and
  shadow-size consistency with Kerr at roughly the 17% level.

RS structural target:

* a tiny positive fractional deviation from pure GR / Kerr, represented
  structurally by `φ⁻⁴⁴`.

The certificate proves two honest facts:

1. The RS structural target is within the current EHT shadow-size and
   circularity sensitivity scales.
2. EHT is **not currently sensitive** to the RS target scale: `φ⁻⁴⁴`
   is far below both 17% and 10%.

This is a consistency / non-sensitivity test, not empirical confirmation.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace EHTM87StrongFieldLikelihood

open IndisputableMonolith.Verification.FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset constants and residuals -/

/-- EHT M87* ring-diameter central value, in microarcseconds. -/
def ehtM87RingDiameterCentralMicroas : ℝ := 42.0

/-- EHT M87* ring-diameter one-sigma uncertainty, in microarcseconds. -/
def ehtM87RingDiameterSigmaMicroas : ℝ := 3.0

/-- Conservative fractional shadow-size sensitivity, using 17% Kerr-consistency scale. -/
def ehtM87ShadowFractionalSigma : ℝ := 0.17

/-- Conservative circularity sensitivity, using the ≤10% circularity-deviation scale. -/
def ehtM87CircularityFractionalSigma : ℝ := 0.10

/-- RS structural target fractional deviation scale, taken from the §7 strong-field attachment. -/
def ehtM87RSTargetScale : ℝ := strongFieldAttachment.rsTargetScale

/-- Residual between current Kerr-consistent central fractional deviation (0) and the RS target. -/
def ehtM87ShadowResidual : ℝ :=
  |0 - ehtM87RSTargetScale|

/-- Residual for circularity channel. -/
def ehtM87CircularityResidual : ℝ :=
  |0 - ehtM87RSTargetScale|

theorem ehtM87ShadowFractionalSigma_pos : 0 < ehtM87ShadowFractionalSigma := by
  unfold ehtM87ShadowFractionalSigma
  norm_num

theorem ehtM87CircularityFractionalSigma_pos :
    0 < ehtM87CircularityFractionalSigma := by
  unfold ehtM87CircularityFractionalSigma
  norm_num

theorem ehtM87RSTargetScale_pos : 0 < ehtM87RSTargetScale := by
  unfold ehtM87RSTargetScale strongFieldAttachment
  norm_num

/-! ## §2. Likelihood-style statements -/

/-- EHT shadow-size channel is compatible with the RS structural target. -/
theorem ehtM87_shadow_residual_lt_sigma :
    ehtM87ShadowResidual < ehtM87ShadowFractionalSigma := by
  unfold ehtM87ShadowResidual ehtM87RSTargetScale
    ehtM87ShadowFractionalSigma strongFieldAttachment
  norm_num

/-- EHT circularity channel is compatible with the RS structural target. -/
theorem ehtM87_circularity_residual_lt_sigma :
    ehtM87CircularityResidual < ehtM87CircularityFractionalSigma := by
  unfold ehtM87CircularityResidual ehtM87RSTargetScale
    ehtM87CircularityFractionalSigma strongFieldAttachment
  norm_num

/-- EHT shadow-size channel is not currently sensitive to `φ⁻⁴⁴`. -/
theorem ehtM87_shadow_sigma_gt_rs_target :
    ehtM87RSTargetScale < ehtM87ShadowFractionalSigma := by
  unfold ehtM87RSTargetScale ehtM87ShadowFractionalSigma strongFieldAttachment
  norm_num

/-- EHT circularity channel is not currently sensitive to `φ⁻⁴⁴`. -/
theorem ehtM87_circularity_sigma_gt_rs_target :
    ehtM87RSTargetScale < ehtM87CircularityFractionalSigma := by
  unfold ehtM87RSTargetScale ehtM87CircularityFractionalSigma strongFieldAttachment
  norm_num

/-- Strong-field dataset attachment is present, positive, and explicitly
marked not currently sensitive. -/
theorem ehtM87_dataset_attachment_status :
    HasPositiveSensitivity strongFieldAttachment ∧
    HasPositiveTargetScale strongFieldAttachment ∧
    strongFieldAttachment.currentlySensitive = false :=
  ⟨strongField_sensitivity_pos, strongField_target_pos, rfl⟩

/-! ## §3. Master cert -/

structure EHTM87StrongFieldLikelihoodCert where
  shadow_sigma_pos : 0 < ehtM87ShadowFractionalSigma
  circularity_sigma_pos : 0 < ehtM87CircularityFractionalSigma
  target_pos : 0 < ehtM87RSTargetScale
  shadow_residual_lt_sigma :
    ehtM87ShadowResidual < ehtM87ShadowFractionalSigma
  circularity_residual_lt_sigma :
    ehtM87CircularityResidual < ehtM87CircularityFractionalSigma
  shadow_not_currently_sensitive :
    ehtM87RSTargetScale < ehtM87ShadowFractionalSigma
  circularity_not_currently_sensitive :
    ehtM87RSTargetScale < ehtM87CircularityFractionalSigma
  dataset_status :
    HasPositiveSensitivity strongFieldAttachment ∧
    HasPositiveTargetScale strongFieldAttachment ∧
    strongFieldAttachment.currentlySensitive = false

def ehtM87StrongFieldLikelihoodCert : EHTM87StrongFieldLikelihoodCert where
  shadow_sigma_pos := ehtM87ShadowFractionalSigma_pos
  circularity_sigma_pos := ehtM87CircularityFractionalSigma_pos
  target_pos := ehtM87RSTargetScale_pos
  shadow_residual_lt_sigma := ehtM87_shadow_residual_lt_sigma
  circularity_residual_lt_sigma := ehtM87_circularity_residual_lt_sigma
  shadow_not_currently_sensitive := ehtM87_shadow_sigma_gt_rs_target
  circularity_not_currently_sensitive := ehtM87_circularity_sigma_gt_rs_target
  dataset_status := ehtM87_dataset_attachment_status

theorem ehtM87StrongFieldLikelihoodCert_inhabited :
    Nonempty EHTM87StrongFieldLikelihoodCert :=
  ⟨ehtM87StrongFieldLikelihoodCert⟩

/-- One-statement EHT M87* likelihood attachment theorem. -/
theorem eht_m87_strong_field_likelihood_one_statement :
    (ehtM87ShadowResidual < ehtM87ShadowFractionalSigma) ∧
    (ehtM87CircularityResidual < ehtM87CircularityFractionalSigma) ∧
    (ehtM87RSTargetScale < ehtM87ShadowFractionalSigma) ∧
    (ehtM87RSTargetScale < ehtM87CircularityFractionalSigma) ∧
    (strongFieldAttachment.currentlySensitive = false) ∧
    Nonempty EHTM87StrongFieldLikelihoodCert :=
  ⟨ehtM87_shadow_residual_lt_sigma,
   ehtM87_circularity_residual_lt_sigma,
   ehtM87_shadow_sigma_gt_rs_target,
   ehtM87_circularity_sigma_gt_rs_target,
   rfl,
   ehtM87StrongFieldLikelihoodCert_inhabited⟩

end

end EHTM87StrongFieldLikelihood
end Verification
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Gravity.StrongFieldStructural
import IndisputableMonolith.Verification.FalsifierRegisterDatasets

/-!
# Cassini Strong-Field Likelihood Attachment

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module upgrades the §7 strong-field falsifier row from a dataset
attachment to a dataset-specific likelihood-style Lean certificate.

Dataset:

* Bertotti-Iess-Tortora Cassini radio-link Shapiro-delay test:
  `γ - 1 = (2.1 ± 2.3) × 10⁻⁵`.

RS structural target:

* `φ⁻⁴⁴ ≈ 6.376×10⁻¹⁰` as recorded in
  `Verification.FalsifierRegisterDatasets.strongFieldAttachment`.

The certificate proves two honest facts:

1. Cassini's central value is statistically compatible with the RS
   structural target at 1σ.
2. Cassini is **not currently sensitive** to the target scale:
   `φ⁻⁴⁴` is far below the reported `2.3×10⁻⁵` one-sigma precision.

This is a consistency / non-sensitivity test, not empirical confirmation.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace CassiniStrongFieldLikelihood

open IndisputableMonolith.Verification.FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset constants and residual -/

/-- Cassini central measurement for the PPN deviation `γ - 1`. -/
def cassiniGammaMinusOneCentral : ℝ := 2.1e-5

/-- Cassini one-sigma uncertainty for `γ - 1`. -/
def cassiniGammaSigma : ℝ := 2.3e-5

/-- RS strong-field structural target scale, taken from the §7 dataset attachment. -/
def cassiniRSTargetScale : ℝ := strongFieldAttachment.rsTargetScale

/-- Residual between Cassini central value and the RS structural target scale. -/
def cassiniStrongFieldResidual : ℝ :=
  |cassiniGammaMinusOneCentral - cassiniRSTargetScale|

theorem cassiniGammaSigma_pos : 0 < cassiniGammaSigma := by
  unfold cassiniGammaSigma
  norm_num

theorem cassiniRSTargetScale_pos : 0 < cassiniRSTargetScale := by
  unfold cassiniRSTargetScale strongFieldAttachment
  norm_num

/-! ## §2. Likelihood-style statements -/

/-- Cassini central value is within 1σ of the RS structural target scale. -/
theorem cassini_residual_lt_one_sigma :
    cassiniStrongFieldResidual < cassiniGammaSigma := by
  unfold cassiniStrongFieldResidual cassiniGammaMinusOneCentral
    cassiniRSTargetScale cassiniGammaSigma strongFieldAttachment
  norm_num

/-- Cassini is not currently sensitive to the φ⁻⁴⁴ target:
the one-sigma uncertainty is larger than the target scale. -/
theorem cassini_sigma_gt_rs_target :
    cassiniRSTargetScale < cassiniGammaSigma := by
  unfold cassiniRSTargetScale cassiniGammaSigma strongFieldAttachment
  norm_num

/-- Cassini dataset attachment is present, positive, and explicitly marked
not currently sensitive. -/
theorem cassini_dataset_attachment_status :
    HasPositiveSensitivity strongFieldAttachment ∧
    HasPositiveTargetScale strongFieldAttachment ∧
    strongFieldAttachment.currentlySensitive = false :=
  ⟨strongField_sensitivity_pos, strongField_target_pos, rfl⟩

/-! ## §3. Master cert -/

structure CassiniStrongFieldLikelihoodCert where
  sigma_pos : 0 < cassiniGammaSigma
  target_pos : 0 < cassiniRSTargetScale
  residual_lt_one_sigma :
    cassiniStrongFieldResidual < cassiniGammaSigma
  not_currently_sensitive :
    cassiniRSTargetScale < cassiniGammaSigma
  dataset_status :
    HasPositiveSensitivity strongFieldAttachment ∧
    HasPositiveTargetScale strongFieldAttachment ∧
    strongFieldAttachment.currentlySensitive = false

def cassiniStrongFieldLikelihoodCert : CassiniStrongFieldLikelihoodCert where
  sigma_pos := cassiniGammaSigma_pos
  target_pos := cassiniRSTargetScale_pos
  residual_lt_one_sigma := cassini_residual_lt_one_sigma
  not_currently_sensitive := cassini_sigma_gt_rs_target
  dataset_status := cassini_dataset_attachment_status

theorem cassiniStrongFieldLikelihoodCert_inhabited :
    Nonempty CassiniStrongFieldLikelihoodCert :=
  ⟨cassiniStrongFieldLikelihoodCert⟩

/-- One-statement Cassini likelihood attachment theorem. -/
theorem cassini_strong_field_likelihood_one_statement :
    (cassiniStrongFieldResidual < cassiniGammaSigma) ∧
    (cassiniRSTargetScale < cassiniGammaSigma) ∧
    (strongFieldAttachment.currentlySensitive = false) ∧
    Nonempty CassiniStrongFieldLikelihoodCert :=
  ⟨cassini_residual_lt_one_sigma,
   cassini_sigma_gt_rs_target,
   rfl,
   cassiniStrongFieldLikelihoodCert_inhabited⟩

end

end CassiniStrongFieldLikelihood
end Verification
end IndisputableMonolith

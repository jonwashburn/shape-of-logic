import Mathlib
import IndisputableMonolith.Verification.FalsifierRegisterDatasets

/-!
# EPTA DR2 PTA Likelihood Attachment

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module adds an EPTA DR2 scalar record to the §7 PTA stochastic-GW
falsifier row.

Dataset handle:

* EPTA DR2 / related analysis reports a stochastic-background spectral
  index around `γ ≈ 3.83`, with approximate asymmetric uncertainty
  `+0.82 / -0.72`, so the recorded interval is approximately
  `γ ∈ (3.11, 4.65)`.

RS structural target:

* `log φ ≈ 0.481`, recorded in
  `Verification.FalsifierRegisterDatasets.ptaAttachment.rsTargetScale`.

Important scope:

* EPTA's `γ` is not the same physical parameter as NANOGrav's running
  index `β` and is not the same as the structural RS placeholder
  `log φ`.
* The cert therefore proves two facts:
  1. EPTA's spectral-index interval is positive, consistent with the
     sign-level fact that the RS structural PTA signature is positive.
  2. A naive magnitude comparison would **not** place `log φ` inside
     the EPTA `γ` interval. This is not an RS falsification, because the
     dynamic RS PTA spectral-index derivation is not yet formalized.

This is a dataset-accounting / scope-control record, not empirical
confirmation.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace EPTAPTALikelihood

open IndisputableMonolith.Verification.FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset interval and target -/

/-- EPTA DR2 representative spectral-index central value. -/
def eptaGammaCentral : ℝ := 3.83

/-- Lower endpoint using the quoted approximate `-0.72` uncertainty. -/
def eptaGammaLower : ℝ := 3.11

/-- Upper endpoint using the quoted approximate `+0.82` uncertainty. -/
def eptaGammaUpper : ℝ := 4.65

/-- Half-width proxy for the EPTA interval. -/
def eptaGammaHalfWidth : ℝ := (eptaGammaUpper - eptaGammaLower) / 2

/-- RS structural PTA target, from the §7 dataset attachment. -/
def eptaRSTarget : ℝ := ptaAttachment.rsTargetScale

/-- Naive residual between EPTA central `γ` and the structural target. -/
def eptaNaiveResidual : ℝ := |eptaGammaCentral - eptaRSTarget|

theorem eptaGammaHalfWidth_pos : 0 < eptaGammaHalfWidth := by
  unfold eptaGammaHalfWidth eptaGammaUpper eptaGammaLower
  norm_num

theorem eptaRSTarget_pos : 0 < eptaRSTarget := by
  unfold eptaRSTarget ptaAttachment
  norm_num

/-! ## §2. Sign compatibility and honest non-match -/

/-- EPTA's spectral-index interval is positive. -/
theorem epta_gamma_interval_positive :
    0 < eptaGammaLower ∧ eptaGammaLower < eptaGammaUpper := by
  unfold eptaGammaLower eptaGammaUpper
  norm_num

/-- The RS structural target is below the EPTA `γ` interval. A naive
magnitude comparison would therefore fail. This is a scope-control
theorem, not a falsification theorem. -/
theorem epta_rs_target_below_gamma_interval :
    eptaRSTarget < eptaGammaLower := by
  unfold eptaRSTarget ptaAttachment eptaGammaLower
  norm_num

/-- The naive residual is larger than the half-width. -/
theorem epta_naive_residual_gt_half_width :
    eptaGammaHalfWidth < eptaNaiveResidual := by
  unfold eptaNaiveResidual eptaGammaCentral eptaRSTarget ptaAttachment
    eptaGammaHalfWidth eptaGammaUpper eptaGammaLower
  norm_num

/-- PTA dataset attachment is present, positive, and explicitly marked
not currently sensitive. -/
theorem epta_dataset_attachment_status :
    HasPositiveSensitivity ptaAttachment ∧
    HasPositiveTargetScale ptaAttachment ∧
    ptaAttachment.currentlySensitive = false :=
  ⟨pta_sensitivity_pos, pta_target_pos, rfl⟩

/-! ## §3. Master cert -/

structure EPTAPTALikelihoodCert where
  interval_positive :
    0 < eptaGammaLower ∧ eptaGammaLower < eptaGammaUpper
  target_pos : 0 < eptaRSTarget
  target_below_gamma_interval :
    eptaRSTarget < eptaGammaLower
  naive_residual_gt_half_width :
    eptaGammaHalfWidth < eptaNaiveResidual
  dataset_status :
    HasPositiveSensitivity ptaAttachment ∧
    HasPositiveTargetScale ptaAttachment ∧
    ptaAttachment.currentlySensitive = false

def eptaPTALikelihoodCert : EPTAPTALikelihoodCert where
  interval_positive := epta_gamma_interval_positive
  target_pos := eptaRSTarget_pos
  target_below_gamma_interval := epta_rs_target_below_gamma_interval
  naive_residual_gt_half_width := epta_naive_residual_gt_half_width
  dataset_status := epta_dataset_attachment_status

theorem eptaPTALikelihoodCert_inhabited :
    Nonempty EPTAPTALikelihoodCert :=
  ⟨eptaPTALikelihoodCert⟩

/-- One-statement EPTA PTA likelihood attachment theorem. -/
theorem epta_pta_likelihood_one_statement :
    (0 < eptaGammaLower ∧ eptaGammaLower < eptaGammaUpper) ∧
    (0 < eptaRSTarget) ∧
    (eptaRSTarget < eptaGammaLower) ∧
    (eptaGammaHalfWidth < eptaNaiveResidual) ∧
    (ptaAttachment.currentlySensitive = false) ∧
    Nonempty EPTAPTALikelihoodCert :=
  ⟨epta_gamma_interval_positive,
   eptaRSTarget_pos,
   epta_rs_target_below_gamma_interval,
   epta_naive_residual_gt_half_width,
   rfl,
   eptaPTALikelihoodCert_inhabited⟩

end

end EPTAPTALikelihood
end Verification
end IndisputableMonolith

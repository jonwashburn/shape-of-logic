import Mathlib
import IndisputableMonolith.Verification.FalsifierRegisterDatasets

/-!
# NANOGrav PTA Likelihood Attachment

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module upgrades the §7 PTA stochastic-GW falsifier row with a
dataset-specific likelihood-style certificate.

Dataset handle:

* NANOGrav 15-year running spectral-index analysis reports a broad
  95% credible interval for the running parameter β consistent with
  zero, approximately `β ∈ [-0.80, 2.96]`.

RS structural target:

* `log φ ≈ 0.481`, recorded in
  `Verification.FalsifierRegisterDatasets.ptaAttachment.rsTargetScale`.

The certificate proves two honest facts:

1. The RS structural target lies inside the reported broad NANOGrav
   95% interval.
2. The interval is not yet a confirmation of RS: the target is much
   smaller than the interval width, and the dataset row remains marked
   not currently sensitive in the falsifier-register attachment.

This is a consistency / non-sensitivity test, not empirical confirmation.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace NANOGravPTALikelihood

open IndisputableMonolith.Verification.FalsifierRegisterDatasets

noncomputable section

/-! ## §1. Dataset interval and target -/

/-- Lower endpoint of the reported broad NANOGrav 95% β interval. -/
def nanogravBetaLower95 : ℝ := -0.80

/-- Upper endpoint of the reported broad NANOGrav 95% β interval. -/
def nanogravBetaUpper95 : ℝ := 2.96

/-- Midpoint of the interval, used only for a likelihood-style residual. -/
def nanogravBetaMidpoint : ℝ := (nanogravBetaLower95 + nanogravBetaUpper95) / 2

/-- Half-width of the 95% interval, used as a conservative sensitivity scale. -/
def nanogravBetaHalfWidth95 : ℝ := (nanogravBetaUpper95 - nanogravBetaLower95) / 2

/-- RS structural PTA target, from the §7 dataset attachment. -/
def nanogravRSTarget : ℝ := ptaAttachment.rsTargetScale

/-- Residual between interval midpoint and RS target. -/
def nanogravPTAResidual : ℝ :=
  |nanogravBetaMidpoint - nanogravRSTarget|

theorem nanogravBetaHalfWidth95_pos : 0 < nanogravBetaHalfWidth95 := by
  unfold nanogravBetaHalfWidth95 nanogravBetaUpper95 nanogravBetaLower95
  norm_num

theorem nanogravRSTarget_pos : 0 < nanogravRSTarget := by
  unfold nanogravRSTarget ptaAttachment
  norm_num

/-! ## §2. Interval inclusion and non-sensitivity -/

/-- The RS structural target lies inside the reported NANOGrav β interval. -/
theorem nanograv_rs_target_inside_95_interval :
    nanogravBetaLower95 < nanogravRSTarget ∧
      nanogravRSTarget < nanogravBetaUpper95 := by
  unfold nanogravBetaLower95 nanogravBetaUpper95 nanogravRSTarget ptaAttachment
  norm_num

/-- Residual from midpoint is smaller than the interval half-width. -/
theorem nanograv_residual_lt_half_width :
    nanogravPTAResidual < nanogravBetaHalfWidth95 := by
  unfold nanogravPTAResidual nanogravBetaMidpoint nanogravBetaHalfWidth95
    nanogravBetaLower95 nanogravBetaUpper95 nanogravRSTarget ptaAttachment
  norm_num

/-- The broad interval is not yet sensitive to the RS target scale:
the half-width is larger than the target itself. -/
theorem nanograv_half_width_gt_rs_target :
    nanogravRSTarget < nanogravBetaHalfWidth95 := by
  unfold nanogravRSTarget ptaAttachment nanogravBetaHalfWidth95
    nanogravBetaUpper95 nanogravBetaLower95
  norm_num

/-- PTA dataset attachment is present, positive, and explicitly marked
not currently sensitive. -/
theorem nanograv_dataset_attachment_status :
    HasPositiveSensitivity ptaAttachment ∧
    HasPositiveTargetScale ptaAttachment ∧
    ptaAttachment.currentlySensitive = false :=
  ⟨pta_sensitivity_pos, pta_target_pos, rfl⟩

/-! ## §3. Master cert -/

structure NANOGravPTALikelihoodCert where
  half_width_pos : 0 < nanogravBetaHalfWidth95
  target_pos : 0 < nanogravRSTarget
  target_inside_interval :
    nanogravBetaLower95 < nanogravRSTarget ∧
      nanogravRSTarget < nanogravBetaUpper95
  residual_lt_half_width :
    nanogravPTAResidual < nanogravBetaHalfWidth95
  not_currently_sensitive :
    nanogravRSTarget < nanogravBetaHalfWidth95
  dataset_status :
    HasPositiveSensitivity ptaAttachment ∧
    HasPositiveTargetScale ptaAttachment ∧
    ptaAttachment.currentlySensitive = false

def nanogravPTALikelihoodCert : NANOGravPTALikelihoodCert where
  half_width_pos := nanogravBetaHalfWidth95_pos
  target_pos := nanogravRSTarget_pos
  target_inside_interval := nanograv_rs_target_inside_95_interval
  residual_lt_half_width := nanograv_residual_lt_half_width
  not_currently_sensitive := nanograv_half_width_gt_rs_target
  dataset_status := nanograv_dataset_attachment_status

theorem nanogravPTALikelihoodCert_inhabited :
    Nonempty NANOGravPTALikelihoodCert :=
  ⟨nanogravPTALikelihoodCert⟩

/-- One-statement NANOGrav PTA likelihood attachment theorem. -/
theorem nanograv_pta_likelihood_one_statement :
    (nanogravBetaLower95 < nanogravRSTarget ∧
      nanogravRSTarget < nanogravBetaUpper95) ∧
    (nanogravPTAResidual < nanogravBetaHalfWidth95) ∧
    (nanogravRSTarget < nanogravBetaHalfWidth95) ∧
    (ptaAttachment.currentlySensitive = false) ∧
    Nonempty NANOGravPTALikelihoodCert :=
  ⟨nanograv_rs_target_inside_95_interval,
   nanograv_residual_lt_half_width,
   nanograv_half_width_gt_rs_target,
   rfl,
   nanogravPTALikelihoodCert_inhabited⟩

end

end NANOGravPTALikelihood
end Verification
end IndisputableMonolith

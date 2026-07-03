import Mathlib
import IndisputableMonolith.Physics.DarkMatterCrossSectionBandScoreCard

/-!
# P0-A6 -- absolute cross-section normalization scorecard

Row ID: P0-A6-01 absolute cross-section normalization.

Predicted formula: `sigma_DM = (sigma_DM/sigma_nu) * sigma_nu_ref`,
where `0.11 < sigma_DM/sigma_nu < 0.13` and the current protocol
normalization is `sigma_nu_ref = 1e-38 cm^2`.

Measurement/protocol target: detector-limit comparisons should use the
derived band `(1.1e-39, 1.3e-39) cm^2` only after a sub-0.35 keV
efficiency curve is supplied.

Falsifier: a detector with valid efficiency at or below 0.35 keV
excluding `sigma_DM ∈ (1.1e-39, 1.3e-39) cm^2` falsifies P0-A6 under
this normalization.

Status: PARTIAL_THEOREM / HYPOTHESIS. The absolute band follows from a
named protocol normalization; deriving that normalization from RS
or a specified neutrino channel remains open.

Lean: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith.Physics.DarkMatterAbsoluteCrossSectionScoreCard

open IndisputableMonolith.Physics.DarkMatterCrossSectionBandScoreCard

noncomputable section

/-- Protocol normalization for the neutrino-reference channel in cm^2. -/
def sigma_nu_reference_cm2 : ℝ := 1e-38

/-- Absolute dark-matter cross-section prediction in cm^2. -/
def sigma_DM_cm2 : ℝ := sigma_DM_over_sigma_nu_RS * sigma_nu_reference_cm2

theorem row_sigma_nu_reference_pos : 0 < sigma_nu_reference_cm2 := by
  unfold sigma_nu_reference_cm2
  norm_num

theorem row_sigma_DM_cm2_band :
    1.1e-39 < sigma_DM_cm2 ∧ sigma_DM_cm2 < 1.3e-39 := by
  unfold sigma_DM_cm2 sigma_nu_reference_cm2
  have h := row_sigma_ratio_band
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

structure DarkMatterAbsoluteCrossSectionScoreCardCert where
  sigma_nu_ref_pos : 0 < sigma_nu_reference_cm2
  sigma_ratio_band :
    0.11 < sigma_DM_over_sigma_nu_RS ∧ sigma_DM_over_sigma_nu_RS < 0.13
  sigma_absolute_band : 1.1e-39 < sigma_DM_cm2 ∧ sigma_DM_cm2 < 1.3e-39

theorem darkMatterAbsoluteCrossSectionScoreCardCert_holds :
    Nonempty DarkMatterAbsoluteCrossSectionScoreCardCert :=
  ⟨{ sigma_nu_ref_pos := row_sigma_nu_reference_pos
     sigma_ratio_band := row_sigma_ratio_band
     sigma_absolute_band := row_sigma_DM_cm2_band }⟩

end

end IndisputableMonolith.Physics.DarkMatterAbsoluteCrossSectionScoreCard

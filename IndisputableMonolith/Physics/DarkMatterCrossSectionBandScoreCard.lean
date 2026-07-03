import Mathlib
import IndisputableMonolith.Constants

/-!
# P0-A6 -- dark-matter cross-section ratio band

Row ID: P0-A6-01 cross-section structural band.

Predicted formula: the native dark-matter cross-section ratio to the
neutrino reference channel is the golden-section recognition quantum
`J(phi) = phi - 3/2`.

Measurement/protocol target: direct-detection exclusion curves must be
compared against this band after detector threshold and efficiency are
locked. This file proves the RS-native ratio band only.

Falsifier: a detector with sufficient sub-keV reach excluding the
cross-section ratio band `(0.11,0.13)` under the locked normalization
falsifies the P0-A6 direct-detection claim.

Status: PARTIAL_THEOREM / HYPOTHESIS. The native ratio band builds;
absolute cross-section normalization and detector-efficiency curves
remain empirical.

Lean: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith.Physics.DarkMatterCrossSectionBandScoreCard

open IndisputableMonolith.Constants

noncomputable section

/-- Native cross-section ratio, `sigma_DM / sigma_nu = J(phi)`. -/
def sigma_DM_over_sigma_nu_RS : ℝ := phi - 3 / 2

theorem row_sigma_ratio_pos : 0 < sigma_DM_over_sigma_nu_RS := by
  unfold sigma_DM_over_sigma_nu_RS
  linarith [phi_gt_onePointSixOne]

theorem row_sigma_ratio_band :
    0.11 < sigma_DM_over_sigma_nu_RS ∧ sigma_DM_over_sigma_nu_RS < 0.13 := by
  unfold sigma_DM_over_sigma_nu_RS
  constructor
  · linarith [phi_gt_onePointSixOne]
  · linarith [phi_lt_onePointSixTwo]

structure DarkMatterCrossSectionBandScoreCardCert where
  sigma_ratio_pos : 0 < sigma_DM_over_sigma_nu_RS
  sigma_ratio_band :
    0.11 < sigma_DM_over_sigma_nu_RS ∧ sigma_DM_over_sigma_nu_RS < 0.13

theorem darkMatterCrossSectionBandScoreCardCert_holds :
    Nonempty DarkMatterCrossSectionBandScoreCardCert :=
  ⟨{ sigma_ratio_pos := row_sigma_ratio_pos
     sigma_ratio_band := row_sigma_ratio_band }⟩

end

end IndisputableMonolith.Physics.DarkMatterCrossSectionBandScoreCard

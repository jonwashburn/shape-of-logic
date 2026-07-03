import Mathlib
import IndisputableMonolith.Constants.FermiConstantScoreCard
import IndisputableMonolith.Physics.DarkMatterCrossSectionBandScoreCard

/-!
# P0-A6 -- weak neutrino-reference cross-section scorecard

Row ID: P0-A6-01 weak reference channel.

Predicted/reference formula:

`sigma_nu_ref = G_F^2 * E_ref^2 * (GeV^-2 -> cm^2)`,

with `E_ref = 1 GeV` and conversion factor `0.3894e-27 cm^2/GeV^-2`.

Measurement/protocol target: this names the neutrino reference channel
used by the P0-A6 cross-section ratio.  It gives
`5.2e-38 < sigma_nu_ref < 5.4e-38 cm^2`, hence
`5.7e-39 < sigma_DM < 7.1e-39 cm^2` from `J(phi)`.

Falsifier: if the named weak reference channel is not the intended
detector normalization, this row must be replaced; if it is the
normalization, a sub-0.35 keV detector excluding the derived band
falsifies P0-A6.

Status: PARTIAL_THEOREM / HYPOTHESIS. The arithmetic follows from the
Fermi scorecard; the choice of a 1 GeV weak reference channel remains
a protocol normalization.

Lean: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith.Physics.DarkMatterWeakReferenceCrossSectionScoreCard

open IndisputableMonolith.Constants.FermiConstantScoreCard
open IndisputableMonolith.Physics.DarkMatterCrossSectionBandScoreCard

noncomputable section

/-- Reference neutrino energy for the weak-channel normalization, in GeV. -/
def E_ref_GeV : ℝ := 1

/-- Conversion `1 GeV^-2 = 0.3894e-27 cm^2`. -/
def gev2_to_cm2 : ℝ := 0.3894e-27

/-- Named weak-channel reference cross-section in cm^2. -/
def sigma_nu_weak_ref_cm2 : ℝ :=
  row_fermi_pred ^ (2 : ℕ) * E_ref_GeV ^ (2 : ℕ) * gev2_to_cm2

/-- Derived absolute dark-matter cross-section in cm^2 on this reference. -/
def sigma_DM_weak_ref_cm2 : ℝ :=
  sigma_DM_over_sigma_nu_RS * sigma_nu_weak_ref_cm2

theorem row_weak_ref_cross_section_band :
    5.2e-38 < sigma_nu_weak_ref_cm2 ∧ sigma_nu_weak_ref_cm2 < 5.4e-38 := by
  unfold sigma_nu_weak_ref_cm2 E_ref_GeV gev2_to_cm2
  have hgf := row_fermi_pred_bracket
  have hgf_pos : 0 < row_fermi_pred := by linarith [hgf.1]
  constructor
  · nlinarith [hgf.1, hgf_pos]
  · nlinarith [hgf.2, hgf_pos]

theorem row_sigma_DM_weak_ref_band :
    5.7e-39 < sigma_DM_weak_ref_cm2 ∧ sigma_DM_weak_ref_cm2 < 7.1e-39 := by
  unfold sigma_DM_weak_ref_cm2
  have href := row_weak_ref_cross_section_band
  have hratio := row_sigma_ratio_band
  have href_pos : 0 < sigma_nu_weak_ref_cm2 := by linarith [href.1]
  have hratio_pos : 0 < sigma_DM_over_sigma_nu_RS := by linarith [hratio.1]
  constructor
  · nlinarith [href.1, hratio.1, href_pos, hratio_pos]
  · nlinarith [href.2, hratio.2, href_pos, hratio_pos]

structure DarkMatterWeakReferenceCrossSectionScoreCardCert where
  weak_ref_band :
    5.2e-38 < sigma_nu_weak_ref_cm2 ∧ sigma_nu_weak_ref_cm2 < 5.4e-38
  sigma_dm_band :
    5.7e-39 < sigma_DM_weak_ref_cm2 ∧ sigma_DM_weak_ref_cm2 < 7.1e-39
  fermi_bracket :
    (1.16e-5 : ℝ) < row_fermi_pred ∧ row_fermi_pred < (1.17e-5 : ℝ)
  sigma_ratio_band :
    0.11 < sigma_DM_over_sigma_nu_RS ∧ sigma_DM_over_sigma_nu_RS < 0.13

theorem darkMatterWeakReferenceCrossSectionScoreCardCert_holds :
    Nonempty DarkMatterWeakReferenceCrossSectionScoreCardCert :=
  ⟨{ weak_ref_band := row_weak_ref_cross_section_band
     sigma_dm_band := row_sigma_DM_weak_ref_band
     fermi_bracket := row_fermi_pred_bracket
     sigma_ratio_band := row_sigma_ratio_band }⟩

end

end IndisputableMonolith.Physics.DarkMatterWeakReferenceCrossSectionScoreCard

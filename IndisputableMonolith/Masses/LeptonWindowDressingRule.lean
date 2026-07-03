import Mathlib
import IndisputableMonolith.Masses.LeptonTorsionSelectionGate

/-!
# Lepton Window Dressing Rule

The previous U4 modules prove three facts:

1. positive screening alone cannot fit the `τ/μ` row;
2. CW-selected `E_pass = 11` torsion reconstructs `τ/μ` with a screening shift in the certified
   lepton-running band;
3. the same CW-selected torsion cannot fit `μ/e` inside that band.

This module packages the resulting **row/window-dependent** dressing rule:

* `μ/e`: screening-dominant, unit torsion;
* `τ/μ`: positive screening times CW-leading `E_pass = 11` torsion.

Both inferred screening shifts land in `(0.015, 0.05)`, and both rows reconstruct exactly. This
does not derive the numerical VP shifts from first-principles logarithmic integrals yet; it gives
the precise two-window operator shape that any such derivation must reproduce.

Lean status: 0 sorry.
-/

namespace IndisputableMonolith
namespace Masses
namespace LeptonWindowDressingRule

open LeptonDisplayDressing
open LeptonDressingFromRecognition
open LeptonTorsionSelectionGate

noncomputable section

/-- The adjacent charged-lepton mass-ratio windows. -/
inductive LeptonWindow where
  | mu_e
  | tau_mu
  deriving DecidableEq, Repr

/-- The observed dressing target in each window. -/
def windowTarget : LeptonWindow → ℝ
  | .mu_e => dressing_mu_e
  | .tau_mu => dressing_tau_mu

/-- Pure-screening shift inferred from the `μ/e` row when torsion is unit. -/
def inferredMuEScreeningShiftPure : ℝ :=
  1 - 1 / dressing_mu_e

/-- Window-dependent screening shift. -/
def windowScreeningShift : LeptonWindow → ℝ
  | .mu_e => inferredMuEScreeningShiftPure
  | .tau_mu => inferredTauMuScreeningShift

/-- Window-dependent torsion factor: unit in the `μ/e` window, CW-leading `E_pass=11` in the
`τ/μ` window. -/
def windowTorsion : LeptonWindow → ℝ
  | .mu_e => 1
  | .tau_mu => epassLinearTorsion

/-- The two-window lepton dressing operator. -/
def windowDressing (w : LeptonWindow) : ℝ :=
  screeningFactor (windowScreeningShift w) * windowTorsion w

/-- The `μ/e` pure-screening shift lies in the same coarse lepton-running band. -/
theorem inferredMuEScreeningShiftPure_in_leptonic_band :
    (0.015 : ℝ) < inferredMuEScreeningShiftPure ∧
    inferredMuEScreeningShiftPure < (0.05 : ℝ) := by
  unfold inferredMuEScreeningShiftPure
  have hd := dressing_mu_e_bounds
  have hdpos : (0 : ℝ) < dressing_mu_e := by linarith
  constructor
  · rw [lt_sub_iff_add_lt]
    have hratio : (1 : ℝ) / dressing_mu_e < (0.985 : ℝ) := by
      rw [div_lt_iff₀ hdpos]
      nlinarith
    linarith
  · rw [sub_lt_iff_lt_add]
    have hratio : (0.95 : ℝ) < (1 : ℝ) / dressing_mu_e := by
      rw [lt_div_iff₀ hdpos]
      nlinarith
    linarith

/-- Sharper bound for the pure-screening shift inferred from the `μ/e` row. -/
theorem inferredMuEScreeningShiftPure_bounds :
    (0.036 : ℝ) < inferredMuEScreeningShiftPure ∧
    inferredMuEScreeningShiftPure < (0.039 : ℝ) := by
  unfold inferredMuEScreeningShiftPure
  have hd := dressing_mu_e_bounds
  have hdpos : (0 : ℝ) < dressing_mu_e := by linarith
  constructor
  · rw [lt_sub_iff_add_lt]
    have hratio : (1 : ℝ) / dressing_mu_e < (0.964 : ℝ) := by
      rw [div_lt_iff₀ hdpos]
      nlinarith
    linarith
  · rw [sub_lt_iff_lt_add]
    have hratio : (0.961 : ℝ) < (1 : ℝ) / dressing_mu_e := by
      rw [lt_div_iff₀ hdpos]
      nlinarith
    linarith

/-- Unit torsion plus pure screening reconstructs the `μ/e` row exactly. -/
theorem mu_e_reconstructed_by_unit_torsion :
    screeningFactor inferredMuEScreeningShiftPure * (1 : ℝ) = dressing_mu_e := by
  unfold inferredMuEScreeningShiftPure screeningFactor
  have hd : (0 : ℝ) < dressing_mu_e := by
    linarith [dressing_mu_e_bounds.1]
  field_simp [ne_of_gt hd]
  ring

/-- The window-dependent screening shift is in the certified lepton-running band for every
adjacent lepton window. -/
theorem windowScreeningShift_in_leptonic_band (w : LeptonWindow) :
    (0.015 : ℝ) < windowScreeningShift w ∧
    windowScreeningShift w < (0.05 : ℝ) := by
  cases w with
  | mu_e =>
      simpa [windowScreeningShift] using inferredMuEScreeningShiftPure_in_leptonic_band
  | tau_mu =>
      simpa [windowScreeningShift] using inferredTauMuScreeningShift_in_leptonic_band

/-- Sharper bound for the screening shift inferred from the `τ/μ` row under CW-selected
`E_pass = 11` torsion. -/
theorem inferredTauMuScreeningShift_bounds :
    (0.015 : ℝ) < inferredTauMuScreeningShift ∧
    inferredTauMuScreeningShift < (0.022 : ℝ) := by
  constructor
  · exact inferredTauMuScreeningShift_in_leptonic_band.1
  · unfold inferredTauMuScreeningShift
    have ht := epassLinearTorsion_bounds
    have hd := dressing_tau_mu_bounds
    have hdpos : (0 : ℝ) < dressing_tau_mu := by linarith
    rw [sub_lt_iff_lt_add]
    have hratio : (0.978 : ℝ) < epassLinearTorsion / dressing_tau_mu := by
      rw [lt_div_iff₀ hdpos]
      nlinarith
    linarith

/-- The two lepton windows require separated screening shifts: `τ/μ` sits below `0.022`,
while `μ/e` sits above `0.036`. -/
theorem windowScreeningShift_separated :
    windowScreeningShift .tau_mu < windowScreeningShift .mu_e := by
  have ht := inferredTauMuScreeningShift_bounds.2
  have hm := inferredMuEScreeningShiftPure_bounds.1
  simp [windowScreeningShift]
  linarith

/-- No single uniform screening shift can be reused across the two adjacent lepton windows. -/
theorem no_uniform_window_screening_shift :
    ¬ ∃ Δ : ℝ, (∀ w : LeptonWindow, windowScreeningShift w = Δ) := by
  rintro ⟨Δ, hΔ⟩
  have hmu : windowScreeningShift .mu_e = Δ := hΔ .mu_e
  have htau : windowScreeningShift .tau_mu = Δ := hΔ .tau_mu
  have hsep := windowScreeningShift_separated
  rw [hmu, htau] at hsep
  exact lt_irrefl Δ hsep

/-- The two-window dressing rule reconstructs the observed dressing target in every adjacent
lepton window. -/
theorem windowDressing_reconstructs (w : LeptonWindow) :
    windowDressing w = windowTarget w := by
  cases w with
  | mu_e =>
      simpa [windowDressing, windowScreeningShift, windowTorsion, windowTarget]
        using mu_e_reconstructed_by_unit_torsion
  | tau_mu =>
      simpa [windowDressing, windowScreeningShift, windowTorsion, windowTarget]
        using tau_mu_reconstructed_by_epass_torsion

/-- The window torsion is not constant across the two adjacent lepton windows. -/
theorem windowTorsion_not_constant :
    windowTorsion .mu_e ≠ windowTorsion .tau_mu := by
  intro h
  have ht : epassLinearTorsion < (0.921 : ℝ) := epassLinearTorsion_bounds.2
  simp [windowTorsion] at h
  linarith

/-- Certificate for the U4 two-window dressing surface. -/
structure LeptonWindowDressingRuleCert where
  screening_band :
    ∀ w : LeptonWindow,
      (0.015 : ℝ) < windowScreeningShift w ∧ windowScreeningShift w < 0.05
  reconstructs :
    ∀ w : LeptonWindow, windowDressing w = windowTarget w
  torsion_not_constant :
    windowTorsion .mu_e ≠ windowTorsion .tau_mu
  screening_not_constant :
    ¬ ∃ Δ : ℝ, (∀ w : LeptonWindow, windowScreeningShift w = Δ)
  mu_e_screening_sharp :
    (0.036 : ℝ) < inferredMuEScreeningShiftPure ∧ inferredMuEScreeningShiftPure < 0.039
  tau_mu_screening_sharp :
    (0.015 : ℝ) < inferredTauMuScreeningShift ∧ inferredTauMuScreeningShift < 0.022
  mu_e_unit_torsion :
    windowTorsion .mu_e = 1
  tau_mu_epass_torsion :
    windowTorsion .tau_mu = epassLinearTorsion

theorem leptonWindowDressingRuleCert_holds :
    Nonempty LeptonWindowDressingRuleCert :=
  ⟨{ screening_band := windowScreeningShift_in_leptonic_band
     reconstructs := windowDressing_reconstructs
     torsion_not_constant := windowTorsion_not_constant
     screening_not_constant := no_uniform_window_screening_shift
     mu_e_screening_sharp := inferredMuEScreeningShiftPure_bounds
     tau_mu_screening_sharp := inferredTauMuScreeningShift_bounds
     mu_e_unit_torsion := rfl
     tau_mu_epass_torsion := rfl }⟩

end

end LeptonWindowDressingRule
end Masses
end IndisputableMonolith

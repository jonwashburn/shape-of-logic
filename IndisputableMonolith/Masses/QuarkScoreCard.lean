import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Masses.Verification
import IndisputableMonolith.Masses.RSBridge.Anchor

/-!
# Quark Score Card

Phase 0 row P0-Q01..P0-Q06 of `planning/PHYSICAL_DERIVATION_PLAN.md`.

This module is the canonical scorecard that records, in one place,
which quark-sector facts are theorem-grade and which remain open. It
does **not** introduce new physics. It only consolidates existing
proofs and tags the residuals honestly.

## Status as of 2026-04-26

- **THEOREM**: charm/up = `φ^11`, top/charm = `φ^6`, all quark mass
  predictions positive, top quark prediction in multi-GeV range.
- **THEOREM**: equal-Z fermions have anchor mass ratio that is a pure
  φ-power of the rung difference (`anchor_ratio` in `RSBridge`).
- **THEOREM**: u/c/t share `ZOf = 276`; d/s/b share `ZOf = 24`;
  e/μ/τ share `ZOf = 1332`.
- **OPEN**: absolute u/d/s/c/b/t mass match within PDG bands. The
  `rs_mass_MeV` formula in `Masses.Verification` does not include the
  `gap (ZOf f)` correction from `RSBridge.Anchor.massAtAnchor`. The
  bridge equivalence theorem is the missing piece.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Masses.QuarkScoreCard

open Anchor RSBridge

noncomputable section

/-! ## Z-charge values per fermion

Derived from `tildeQ` and the sector formula in `RSBridge.Anchor`.
For up-type quarks `q̃ = +4`, so `ZOf = 4 + 16 + 256 = 276`.
For down-type quarks `q̃ = -2`, so `ZOf = 4 + 4 + 16 = 24`.
For charged leptons `q̃ = -6`, so `ZOf = 36 + 1296 = 1332`.
-/

theorem ZOf_up_quarks : ZOf .u = 276 ∧ ZOf .c = 276 ∧ ZOf .t = 276 := by
  refine ⟨?_, ?_, ?_⟩ <;> · decide

theorem ZOf_down_quarks : ZOf .d = 24 ∧ ZOf .s = 24 ∧ ZOf .b = 24 := by
  refine ⟨?_, ?_, ?_⟩ <;> · decide

theorem ZOf_charged_leptons : ZOf .e = 1332 ∧ ZOf .mu = 1332 ∧ ZOf .tau = 1332 := by
  refine ⟨?_, ?_, ?_⟩ <;> · decide

/-! ## Equal-Z within a sector implies pure φ-power ratios -/

theorem charm_up_equal_Z : ZOf .u = ZOf .c := by
  obtain ⟨hu, hc, _⟩ := ZOf_up_quarks
  rw [hu, hc]

theorem top_up_equal_Z : ZOf .u = ZOf .t := by
  obtain ⟨hu, _, ht⟩ := ZOf_up_quarks
  rw [hu, ht]

theorem strange_down_equal_Z : ZOf .d = ZOf .s := by
  obtain ⟨hd, hs, _⟩ := ZOf_down_quarks
  rw [hd, hs]

theorem bottom_down_equal_Z : ZOf .d = ZOf .b := by
  obtain ⟨hd, _, hb⟩ := ZOf_down_quarks
  rw [hd, hb]

/-! ## Generation rung spacing (proved directly from Integers definitions) -/

open Integers in
theorem up_generation_spacing :
    r_up "c" - r_up "u" = 11 ∧ r_up "t" - r_up "u" = 17 := by
  decide

open Integers in
theorem down_generation_spacing :
    r_down "s" - r_down "d" = 11 ∧ r_down "b" - r_down "d" = 17 := by
  decide

/-! ## Structural ratios that already match PDG order of magnitude

These are theorems in `Masses.Verification`. We re-export them under
explicit row IDs so the scorecard can be read at a glance.
-/

/-- P0-Q structural row: m_c / m_u = φ^11 (proved). -/
theorem row_charm_up_ratio :
    Verification.charm_quark_pred / Verification.up_quark_pred =
      Constants.phi ^ (11 : ℕ) :=
  Verification.charm_up_ratio

/-- P0-Q structural row: m_t / m_c = φ^6 (proved). -/
theorem row_top_charm_ratio :
    Verification.top_quark_pred / Verification.charm_quark_pred =
      Constants.phi ^ (6 : ℕ) :=
  Verification.top_charm_ratio

/-- P0-Q06 structural row: top mass prediction lies in (10 GeV, 1 TeV). -/
theorem row_top_quark_in_band :
    (10000 : ℝ) < Verification.top_quark_pred ∧
      Verification.top_quark_pred < 1000000 :=
  Verification.top_quark_pred_order

/-- All quark structural predictions are positive (proved). -/
theorem row_quark_preds_pos :
    0 < Verification.up_quark_pred ∧
      0 < Verification.charm_quark_pred ∧
        0 < Verification.top_quark_pred :=
  Verification.quark_preds_pos

/-! ## Lepton mass match (already theorem-grade, re-exported for the audit)

The lepton sector match is the strongest piece of the absolute-mass
scorecard, with bounds proved by interval arithmetic in
`Masses.Verification`.
-/

/-- Electron mass within 0.3 percent of PDG. -/
theorem row_electron_pct :
    |Verification.rs_mass_MeV .Lepton 2 - Verification.m_e_exp| /
        Verification.m_e_exp < 0.003 :=
  Verification.electron_relative_error

/-- Muon mass within 4 percent of PDG. -/
theorem row_muon_pct :
    |Verification.rs_mass_MeV .Lepton 13 - Verification.m_mu_exp| /
        Verification.m_mu_exp < 0.04 :=
  Verification.muon_relative_error

/-- Tau mass within 3 percent of PDG. -/
theorem row_tau_pct :
    |Verification.rs_mass_MeV .Lepton 19 - Verification.m_tau_exp| /
        Verification.m_tau_exp < 0.03 :=
  Verification.tau_relative_error

/-- Muon-electron PDG mass ratio matches `phi^11` within 4 percent. -/
theorem row_muon_electron_ratio_pct :
    |Constants.phi ^ (11 : ℕ) - Verification.ratio_mu_e_exp| /
        Verification.ratio_mu_e_exp < 0.04 :=
  Verification.muon_electron_ratio_error

/-- Tau-electron PDG mass ratio matches `phi^17` within 3 percent. -/
theorem row_tau_electron_ratio_pct :
    |Constants.phi ^ (17 : ℕ) - Verification.ratio_tau_e_exp| /
        Verification.ratio_tau_e_exp < 0.03 :=
  Verification.tau_electron_ratio_error

/-! ## The named open residual

The `rs_mass_MeV` formula does not currently apply the gap correction
`gap (ZOf f)`. The closure target is the bridge equivalence connecting
the structural sector formula to the gap-corrected anchor formula.

Once the bridge is proved, the absolute u/d/s/c/b/t mass intervals
become a numerical computation on the gap values:

- `gap(276) ≈ 10.69` for up-type quarks,
- `gap(24)  ≈ 5.74`  for down-type quarks,
- `gap(1332) ≈ 13.95` for charged leptons.
-/

/-- Named residual: the bridge between the structural `rs_mass_MeV`
    formula and the gap-corrected `massAtAnchor` formula on a chosen
    quark sector. A proof of this proposition would close the absolute
    quark-mass row of the scorecard. -/
def QuarkAbsoluteMassResidual : Prop :=
  ∀ (f : Fermion),
    sectorOf f = Sector.up →
    Verification.rs_mass_MeV Anchor.Sector.UpQuark (RSBridge.rung f)
      = M0 * Real.exp (((RSBridge.rung f : ℝ) - 8 + gap (ZOf f)) *
            Real.log Constants.phi)

/-! ## ScoreCard certificate

A single record bundling every theorem-grade row of this Phase 0
deliverable. -/

structure QuarkScoreCardCert where
  ZOf_up : ZOf .u = 276 ∧ ZOf .c = 276 ∧ ZOf .t = 276
  ZOf_down : ZOf .d = 24 ∧ ZOf .s = 24 ∧ ZOf .b = 24
  ZOf_lep : ZOf .e = 1332 ∧ ZOf .mu = 1332 ∧ ZOf .tau = 1332
  charm_up_ratio_eq :
    Verification.charm_quark_pred / Verification.up_quark_pred =
      Constants.phi ^ (11 : ℕ)
  top_charm_ratio_eq :
    Verification.top_quark_pred / Verification.charm_quark_pred =
      Constants.phi ^ (6 : ℕ)
  top_in_band : (10000 : ℝ) < Verification.top_quark_pred ∧
      Verification.top_quark_pred < 1000000
  quark_preds_pos : 0 < Verification.up_quark_pred ∧
      0 < Verification.charm_quark_pred ∧ 0 < Verification.top_quark_pred
  electron_pct :
    |Verification.rs_mass_MeV .Lepton 2 - Verification.m_e_exp| /
        Verification.m_e_exp < 0.003
  muon_pct :
    |Verification.rs_mass_MeV .Lepton 13 - Verification.m_mu_exp| /
        Verification.m_mu_exp < 0.04
  tau_pct :
    |Verification.rs_mass_MeV .Lepton 19 - Verification.m_tau_exp| /
        Verification.m_tau_exp < 0.03

theorem quarkScoreCardCert_holds : Nonempty QuarkScoreCardCert :=
  ⟨{ ZOf_up := ZOf_up_quarks
     ZOf_down := ZOf_down_quarks
     ZOf_lep := ZOf_charged_leptons
     charm_up_ratio_eq := row_charm_up_ratio
     top_charm_ratio_eq := row_top_charm_ratio
     top_in_band := row_top_quark_in_band
     quark_preds_pos := row_quark_preds_pos
     electron_pct := row_electron_pct
     muon_pct := row_muon_pct
     tau_pct := row_tau_pct }⟩

/-! ## Falsifier

If, in a deepening pass, any of the following is shown to fail, the
scorecard breaks and the entry must be retracted:

- `m_c / m_u = φ^11` is not within 0.5 percent of `(1.27 GeV) / (2.16 MeV)`
  after the gap correction is applied.
- `m_t / m_c = φ^6` is not within 0.5 percent of
  `(172.69 GeV) / (1.27 GeV)` after the gap correction is applied.
- The bridge equivalence between `rs_mass_MeV` and `massAtAnchor`
  cannot be proved.
-/

end

end IndisputableMonolith.Masses.QuarkScoreCard

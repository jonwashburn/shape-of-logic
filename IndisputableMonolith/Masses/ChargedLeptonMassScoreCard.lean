import Mathlib
import IndisputableMonolith.Masses.QuarkScoreCard
import IndisputableMonolith.Masses.Verification
import IndisputableMonolith.Constants

/-!
# Phase 2 — P2-LEP: charged lepton masses `e`, `μ`, `τ`

**Predicted (RS):** `Verification.rs_mass_MeV` on lepton rungs 2, 13, 19 with
`ZOf = 1332` (charged leptons), versus PDG reference masses in `Verification` (`m_e_exp`, …).

**Falsifier (one sentence):** A PDG update that places any of the three masses outside the
stated percent bands once the `rs_mass_MeV` rung map is held fixed falsifies the mass row.

**Status:** `PARTIAL_THEOREM` on relative error and mass-ratio ladders; the same gap/anchor
residual as quarks remains if one demands `rs_mass_MeV = M0 * exp((rung-8+gap) log φ)`.

**Lean: 0 sorry, 0 new axiom**
-/

namespace IndisputableMonolith.Masses.ChargedLeptonMassScoreCard

open IndisputableMonolith.Masses.QuarkScoreCard
open IndisputableMonolith.Masses.Verification
open IndisputableMonolith.Constants

noncomputable section

theorem row_electron_rel :
    |rs_mass_MeV .Lepton 2 - m_e_exp| / m_e_exp < 0.003 := row_electron_pct

theorem row_muon_rel :
    |rs_mass_MeV .Lepton 13 - m_mu_exp| / m_mu_exp < 0.04 := row_muon_pct

theorem row_tau_rel :
    |rs_mass_MeV .Lepton 19 - m_tau_exp| / m_tau_exp < 0.03 := row_tau_pct

theorem row_muon_electron_ratio :
    |phi ^ (11 : ℕ) - ratio_mu_e_exp| / ratio_mu_e_exp < 0.04 := row_muon_electron_ratio_pct

theorem row_tau_electron_ratio :
    |phi ^ (17 : ℕ) - ratio_tau_e_exp| / ratio_tau_e_exp < 0.03 := row_tau_electron_ratio_pct

structure ChargedLeptonMassScoreCardCert where
  electron : |rs_mass_MeV .Lepton 2 - m_e_exp| / m_e_exp < 0.003
  muon : |rs_mass_MeV .Lepton 13 - m_mu_exp| / m_mu_exp < 0.04
  tau : |rs_mass_MeV .Lepton 19 - m_tau_exp| / m_tau_exp < 0.03
  muon_e : |phi ^ (11 : ℕ) - ratio_mu_e_exp| / ratio_mu_e_exp < 0.04
  tau_e : |phi ^ (17 : ℕ) - ratio_tau_e_exp| / ratio_tau_e_exp < 0.03

theorem chargedLeptonMassScoreCardCert_holds : Nonempty ChargedLeptonMassScoreCardCert :=
  ⟨{ electron := row_electron_rel
     muon := row_muon_rel
     tau := row_tau_rel
     muon_e := row_muon_electron_ratio
     tau_e := row_tau_electron_ratio }⟩

end

end IndisputableMonolith.Masses.ChargedLeptonMassScoreCard

import Mathlib
import IndisputableMonolith.Masses.LeptonTorsionLinearCandidate

/-!
# Lepton Torsion Selection Gate

`LeptonTorsionLinearCandidate` proves that the linear ansatz

```
τ(k) = 1 - k α_RS
```

can match the U4 torsion window only for the middle cube-count band. Four Q₃ counts survive:

* `E_pass = 11`
* `E = 12`
* `V + F - C = 13`
* `V + F = 14`

This module prevents the next common mistake: silently picking one of those four because it
looks good numerically. The surviving band is not a derivation. A derivation must supply a
structural selector. We formalize that selection gate:

* the broad "middle band" predicate is not unique;
* each sharper structural selector is unique, but is a new physical claim;
* the existing CW-filtration theorem for the lepton ladder selects the passive-edge candidate.

Lean status: 0 sorry.
-/

namespace IndisputableMonolith
namespace Masses
namespace LeptonTorsionSelectionGate

open LeptonTorsionLinearCandidate
open SectorDependentTorsion
open LeptonDressingFromRecognition
open LeptonDisplayDressing

noncomputable section

/-- The finite list of cube-count candidates currently under consideration for the linear
lepton torsion coefficient. -/
inductive TorsionCandidate where
  | Epass
  | E
  | VFminusC
  | VF
  | F
  | W
  deriving DecidableEq, Repr

/-- The real coefficient attached to each candidate. -/
def coeff : TorsionCandidate → ℝ
  | .Epass => coeff_Epass
  | .E => coeff_E
  | .VFminusC => coeff_VFminusC
  | .VF => coeff_VF
  | .F => coeff_F
  | .W => coeff_W

/-- Candidate survives the linear torsion window. -/
def survivesLinearWindow (c : TorsionCandidate) : Prop :=
  (0.889 : ℝ) < linearTorsionCoeff (coeff c) ∧
    linearTorsionCoeff (coeff c) < 0.939

theorem Epass_survives : survivesLinearWindow .Epass := by
  simpa [survivesLinearWindow, coeff] using Epass_linear_torsion_in_window

theorem E_survives : survivesLinearWindow .E := by
  simpa [survivesLinearWindow, coeff] using E_linear_torsion_in_window

theorem VFminusC_survives : survivesLinearWindow .VFminusC := by
  simpa [survivesLinearWindow, coeff] using VFminusC_linear_torsion_in_window

theorem VF_survives : survivesLinearWindow .VF := by
  simpa [survivesLinearWindow, coeff] using VF_linear_torsion_in_window

theorem F_rejected : ¬ survivesLinearWindow .F := by
  intro h
  have tooHigh : (0.939 : ℝ) < linearTorsionCoeff (coeff .F) := by
    simpa [coeff] using F_linear_torsion_too_high
  linarith [h.2]

theorem W_rejected : ¬ survivesLinearWindow .W := by
  intro h
  have tooLow : linearTorsionCoeff (coeff .W) < (0.889 : ℝ) := by
    simpa [coeff] using W_linear_torsion_too_low
  linarith [h.1]

/-- A predicate uniquely selects a torsion candidate. -/
def UniqueSelector (P : TorsionCandidate → Prop) : Prop :=
  ∃ c, P c ∧ ∀ d, P d → d = c

/-- The broad surviving-window predicate is not a selector: it admits at least `E_pass` and `E`. -/
theorem survivesLinearWindow_not_unique :
    ¬ UniqueSelector survivesLinearWindow := by
  rintro ⟨c, hc, huniq⟩
  have h1 : TorsionCandidate.Epass = c := huniq .Epass Epass_survives
  have h2 : TorsionCandidate.E = c := huniq .E E_survives
  have hneq : TorsionCandidate.Epass ≠ TorsionCandidate.E := by decide
  exact hneq (h1.trans h2.symm)

/-! ## Structural selectors

Each selector below is unique by construction. The point is epistemic: using one of them is a
new physical claim about the recognition source. Lean can certify the consequence, but the
selector itself must be derived elsewhere.
-/

def selectsPassiveEdge : TorsionCandidate → Prop
  | .Epass => True
  | _ => False

def selectsTotalEdge : TorsionCandidate → Prop
  | .E => True
  | _ => False

def selectsBoundaryExcess : TorsionCandidate → Prop
  | .VFminusC => True
  | _ => False

def selectsVertexFaceShell : TorsionCandidate → Prop
  | .VF => True
  | _ => False

theorem passive_edge_selector_unique :
    UniqueSelector selectsPassiveEdge := by
  refine ⟨.Epass, by simp [selectsPassiveEdge], ?_⟩
  intro d hd
  cases d <;> simp [selectsPassiveEdge] at hd ⊢

theorem total_edge_selector_unique :
    UniqueSelector selectsTotalEdge := by
  refine ⟨.E, by simp [selectsTotalEdge], ?_⟩
  intro d hd
  cases d <;> simp [selectsTotalEdge] at hd ⊢

theorem boundary_excess_selector_unique :
    UniqueSelector selectsBoundaryExcess := by
  refine ⟨.VFminusC, by simp [selectsBoundaryExcess], ?_⟩
  intro d hd
  cases d <;> simp [selectsBoundaryExcess] at hd ⊢

theorem vertex_face_shell_selector_unique :
    UniqueSelector selectsVertexFaceShell := by
  refine ⟨.VF, by simp [selectsVertexFaceShell], ?_⟩
  intro d hd
  cases d <;> simp [selectsVertexFaceShell] at hd ⊢

/-- Every sharp structural selector above lands inside the torsion window. -/
theorem every_sharp_selector_survives :
    (∀ c, selectsPassiveEdge c → survivesLinearWindow c) ∧
    (∀ c, selectsTotalEdge c → survivesLinearWindow c) ∧
    (∀ c, selectsBoundaryExcess c → survivesLinearWindow c) ∧
    (∀ c, selectsVertexFaceShell c → survivesLinearWindow c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    cases c <;> simp [selectsPassiveEdge] at hc
    exact Epass_survives
  · intro c hc
    cases c <;> simp [selectsTotalEdge] at hc
    exact E_survives
  · intro c hc
    cases c <;> simp [selectsBoundaryExcess] at hc
    exact VFminusC_survives
  · intro c hc
    cases c <;> simp [selectsVertexFaceShell] at hc
    exact VF_survives

/-! ## CW-filtration selector

`SectorDependentTorsion.uniformCW_reproduces_lepton` is stronger than a numeric filter. It says
the CW-filtration rule that reproduces the lepton ladder at coupling dimension `d=1` has leading
step `(E−1) = E_pass`. If the U4 compensating torsion uses the same lepton CW-leading source,
the passive-edge selector is forced.
-/

/-- The leading coefficient selected by the lepton CW-filtration source. -/
def leptonCWLeadingCoeff : ℝ :=
  ((uniformCWStep 1).1 : ℝ)

theorem leptonCWLeadingCoeff_eq_Epass :
    leptonCWLeadingCoeff = coeff_Epass := by
  unfold leptonCWLeadingCoeff coeff_Epass
  rw [uniformCW_reproduces_lepton]

/-- Candidate `c` is selected by the same CW-leading source that derives the lepton ladder. -/
def selectedByLeptonCWLeading (c : TorsionCandidate) : Prop :=
  coeff c = leptonCWLeadingCoeff

theorem leptonCW_selects_Epass :
    selectedByLeptonCWLeading .Epass := by
  unfold selectedByLeptonCWLeading
  rw [leptonCWLeadingCoeff_eq_Epass]
  simp [coeff]

theorem leptonCW_selector_unique :
    UniqueSelector selectedByLeptonCWLeading := by
  refine ⟨.Epass, leptonCW_selects_Epass, ?_⟩
  intro d hd
  cases d <;>
    simp [selectedByLeptonCWLeading, coeff, leptonCWLeadingCoeff_eq_Epass,
      coeff_Epass_eq, coeff_E_eq, coeff_VFminusC_eq, coeff_VF_eq, coeff_F_eq, coeff_W_eq] at hd ⊢

theorem leptonCW_selected_candidate_survives :
    ∀ c, selectedByLeptonCWLeading c → survivesLinearWindow c := by
  intro c hc
  have hsel := (Exists.choose_spec leptonCW_selector_unique)
  cases c <;>
    simp [selectedByLeptonCWLeading, coeff, leptonCWLeadingCoeff_eq_Epass,
      coeff_Epass_eq, coeff_E_eq, coeff_VFminusC_eq, coeff_VF_eq, coeff_F_eq, coeff_W_eq] at hc ⊢
  exact Epass_survives

/-! ## τ/μ reconstruction with the CW-selected candidate

Once the CW-leading selector chooses `E_pass = 11`, the linear torsion factor is no longer free:
it is `1 - 11α_RS`. The observed `τ/μ` dressing then determines the screening shift required to
reconstruct the row. The theorem below proves that this inferred shift lies inside the already
certified lepton-running band `(0.015, 0.05)`.

This is not yet a first-principles derivation of the running magnitude; it is a consistency and
closure theorem: the CW-selected torsion candidate is compatible with the lepton VP running band
and reconstructs the row exactly.
-/

def epassLinearTorsion : ℝ :=
  linearTorsionCoeff coeff_Epass

def inferredTauMuScreeningShift : ℝ :=
  1 - epassLinearTorsion / dressing_tau_mu

theorem epassLinearTorsion_bounds :
    (0.919 : ℝ) < epassLinearTorsion ∧ epassLinearTorsion < (0.921 : ℝ) := by
  unfold epassLinearTorsion linearTorsionCoeff
  rw [coeff_Epass_eq]
  constructor
  · nlinarith [alphaRS_lt_00073, alphaRS_pos]
  · nlinarith [alphaRS_gt_00072, alphaRS_pos]

theorem inferredTauMuScreeningShift_in_leptonic_band :
    (0.015 : ℝ) < inferredTauMuScreeningShift ∧
    inferredTauMuScreeningShift < (0.05 : ℝ) := by
  unfold inferredTauMuScreeningShift
  have ht := epassLinearTorsion_bounds
  have hd := dressing_tau_mu_bounds
  have hdpos : (0 : ℝ) < dressing_tau_mu := by linarith
  constructor
  · rw [lt_sub_iff_add_lt]
    have hratio : epassLinearTorsion / dressing_tau_mu < (0.985 : ℝ) := by
      rw [div_lt_iff₀ hdpos]
      nlinarith
    linarith
  · rw [sub_lt_iff_lt_add]
    have hratio : (0.95 : ℝ) < epassLinearTorsion / dressing_tau_mu := by
      rw [lt_div_iff₀ hdpos]
      nlinarith
    linarith

theorem tau_mu_reconstructed_by_epass_torsion :
    screeningFactor inferredTauMuScreeningShift * epassLinearTorsion = dressing_tau_mu := by
  unfold inferredTauMuScreeningShift screeningFactor
  have ht : (0 : ℝ) < epassLinearTorsion := by
    linarith [epassLinearTorsion_bounds.1]
  have hd : (0 : ℝ) < dressing_tau_mu := by
    linarith [dressing_tau_mu_bounds.1]
  field_simp [ne_of_gt ht, ne_of_gt hd]
  ring

/-! ## The same CW-selected torsion cannot fit both lepton rows

The `E_pass = 11` candidate reconstructs `τ/μ` with a screening shift in the lepton VP band.
It does **not** reconstruct `μ/e` within that band. If one forces the same torsion into the
`μ/e` row, the inferred screening shift exceeds `0.05`, outside the certified lepton-running
window. This is the next real U4 obstruction: the lepton dressing is not a single
`screening(Δ) * (1 - 11α)` block reused across all adjacent-generation windows.
-/

def inferredMuEScreeningShiftFromEpass : ℝ :=
  1 - epassLinearTorsion / dressing_mu_e

theorem inferredMuEScreeningShiftFromEpass_gt_005 :
    (0.05 : ℝ) < inferredMuEScreeningShiftFromEpass := by
  unfold inferredMuEScreeningShiftFromEpass
  have ht := epassLinearTorsion_bounds
  have hd := dressing_mu_e_bounds
  have hdpos : (0 : ℝ) < dressing_mu_e := by linarith
  rw [lt_sub_iff_add_lt]
  have hratio : epassLinearTorsion / dressing_mu_e < (0.95 : ℝ) := by
    rw [div_lt_iff₀ hdpos]
    nlinarith
  linarith

theorem mu_e_reconstructed_by_epass_torsion_outside_band :
    screeningFactor inferredMuEScreeningShiftFromEpass * epassLinearTorsion = dressing_mu_e ∧
    (0.05 : ℝ) < inferredMuEScreeningShiftFromEpass := by
  constructor
  · unfold inferredMuEScreeningShiftFromEpass screeningFactor
    have ht : (0 : ℝ) < epassLinearTorsion := by
      linarith [epassLinearTorsion_bounds.1]
    have hd : (0 : ℝ) < dressing_mu_e := by
      linarith [dressing_mu_e_bounds.1]
    field_simp [ne_of_gt ht, ne_of_gt hd]
    ring
  · exact inferredMuEScreeningShiftFromEpass_gt_005

/-- No certified lepton-band screening shift can reconstruct the `μ/e` row using the same
CW-selected `E_pass = 11` torsion factor. -/
theorem no_mu_e_epass_reconstruction_in_leptonic_band :
    ¬ ∃ Δ : ℝ, (0.015 : ℝ) < Δ ∧ Δ < 0.05 ∧
      screeningFactor Δ * epassLinearTorsion = dressing_mu_e := by
  rintro ⟨Δ, hΔlo, hΔhi, hmatch⟩
  have hden : 0 < 1 - Δ := by linarith
  have hmul : epassLinearTorsion = dressing_mu_e * (1 - Δ) := by
    have htmp := congrArg (fun x => x * (1 - Δ)) hmatch
    unfold screeningFactor at htmp
    field_simp [ne_of_gt hden] at htmp
    linarith
  nlinarith [epassLinearTorsion_bounds.2, dressing_mu_e_bounds.1, hΔhi, hmul]

/-- Certificate for the U4 selection gate. -/
structure LeptonTorsionSelectionGateCert where
  broad_window_not_selector : ¬ UniqueSelector survivesLinearWindow
  F_not_survive : ¬ survivesLinearWindow .F
  W_not_survive : ¬ survivesLinearWindow .W
  passive_edge_unique : UniqueSelector selectsPassiveEdge
  total_edge_unique : UniqueSelector selectsTotalEdge
  boundary_excess_unique : UniqueSelector selectsBoundaryExcess
  vertex_face_shell_unique : UniqueSelector selectsVertexFaceShell
  lepton_cw_unique : UniqueSelector selectedByLeptonCWLeading
  lepton_cw_survives : ∀ c, selectedByLeptonCWLeading c → survivesLinearWindow c
  epass_inferred_delta_band :
    (0.015 : ℝ) < inferredTauMuScreeningShift ∧ inferredTauMuScreeningShift < 0.05
  epass_reconstructs_tau_mu :
    screeningFactor inferredTauMuScreeningShift * epassLinearTorsion = dressing_tau_mu
  epass_mu_e_forbidden_in_band :
    ¬ ∃ Δ : ℝ, (0.015 : ℝ) < Δ ∧ Δ < 0.05 ∧
      screeningFactor Δ * epassLinearTorsion = dressing_mu_e
  sharp_selectors_survive :
    (∀ c, selectsPassiveEdge c → survivesLinearWindow c) ∧
    (∀ c, selectsTotalEdge c → survivesLinearWindow c) ∧
    (∀ c, selectsBoundaryExcess c → survivesLinearWindow c) ∧
    (∀ c, selectsVertexFaceShell c → survivesLinearWindow c)

theorem leptonTorsionSelectionGateCert_holds :
    Nonempty LeptonTorsionSelectionGateCert :=
  ⟨{ broad_window_not_selector := survivesLinearWindow_not_unique
     F_not_survive := F_rejected
     W_not_survive := W_rejected
     passive_edge_unique := passive_edge_selector_unique
     total_edge_unique := total_edge_selector_unique
     boundary_excess_unique := boundary_excess_selector_unique
     vertex_face_shell_unique := vertex_face_shell_selector_unique
     lepton_cw_unique := leptonCW_selector_unique
     lepton_cw_survives := leptonCW_selected_candidate_survives
     epass_inferred_delta_band := inferredTauMuScreeningShift_in_leptonic_band
     epass_reconstructs_tau_mu := tau_mu_reconstructed_by_epass_torsion
     epass_mu_e_forbidden_in_band := no_mu_e_epass_reconstruction_in_leptonic_band
     sharp_selectors_survive := every_sharp_selector_survives }⟩

end

end LeptonTorsionSelectionGate
end Masses
end IndisputableMonolith

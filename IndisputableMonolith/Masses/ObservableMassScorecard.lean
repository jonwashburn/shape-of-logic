import Mathlib
import IndisputableMonolith.Masses.MassEpistemics
import IndisputableMonolith.Masses.ChargedLeptonMassScoreCard
import IndisputableMonolith.Masses.ZBosonMassScoreCard
import IndisputableMonolith.Masses.QuarkAbsoluteBridgeScoreCard
import IndisputableMonolith.Masses.NeutrinoMajoranaLadder

/-!
# Observable-first mass scorecard

This module implements the first execution item in
`Mass_Framework_Total_Closure_Plan_20260530.html`.

The point is not to add another numerical table. It is to force every mass row
to declare what kind of object is being compared:

* intrinsic recognition rest load;
* near-direct / kinematic observable;
* resonance observable;
* reconstructed template parameter;
* Standard Model scheme parameter;
* difference-only observable;
* composite binding observable.

The main theorem-level consequence is simple and important:
confined quark MS-bar rows and absolute neutrino rows are **not legitimate
direct mass comparisons**. Charged leptons and the Z row may carry ordinary
scorecard certificates because their quoted masses track observables closely
enough to test the intrinsic ladder plus display dressing.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace ObservableMassScorecard

open MassEpistemics

/-! ## Comparison targets -/

/-- What kind of target a mass row is trying to compare against. -/
inductive ComparisonTarget where
  /-- Recognition-native mass before any laboratory display map. -/
  | intrinsicRestLoad
  /-- Near-direct inertial / kinematic rest mass of an asymptotic state. -/
  | directObservable
  /-- Resonance line-shape peak or invariant-mass bump. -/
  | resonanceObservable
  /-- Template-level reconstructed distribution, e.g. W transverse mass or top MC mass. -/
  | reconstructedTemplate
  /-- Renormalization-scheme parameter, e.g. MS-bar confined-quark mass. -/
  | schemeParameter
  /-- Oscillation/difference-only observable with no absolute mass scale measured. -/
  | differenceOnly
  /-- Composite binding-energy observable, e.g. proton/neutron mass. -/
  | compositeBinding
deriving DecidableEq, Repr

/-- The action required before the row can be used as a mass test. -/
inductive ComparisonVerdict where
  /-- Direct enough to test an intrinsic row plus known dressing. -/
  | directCheck
  /-- Compare, but only after deriving the display/dressing operator. -/
  | dressingRequired
  /-- Compare at template-distribution level, not as a direct rest weight. -/
  | templateRequired
  /-- Stop: derive the scheme bridge or compare to a scheme-free observable. -/
  | bridgeRequired
  /-- Compare ratios/splittings only; absolute mass is not observed. -/
  | ratioOnly
  /-- Requires a binding operator, not a current-mass bridge. -/
  | bindingRequired
deriving DecidableEq, Repr

/-- One observable-first row. -/
structure ObservableMassRow where
  particle : Particle
  target : ComparisonTarget
  verdict : ComparisonVerdict
deriving DecidableEq, Repr

open Particle ComparisonTarget ComparisonVerdict ObservedSignal

/-- Canonical observable-first classification derived from `MassEpistemics`. -/
def rowOf : Particle → ObservableMassRow
  | electron => ⟨electron, directObservable, directCheck⟩
  | muon => ⟨muon, directObservable, dressingRequired⟩
  | tau => ⟨tau, directObservable, dressingRequired⟩
  | zBoson => ⟨zBoson, resonanceObservable, directCheck⟩
  | higgs => ⟨higgs, resonanceObservable, dressingRequired⟩
  | wBoson => ⟨wBoson, reconstructedTemplate, templateRequired⟩
  | top => ⟨top, reconstructedTemplate, templateRequired⟩
  | up => ⟨up, schemeParameter, bridgeRequired⟩
  | down => ⟨down, schemeParameter, bridgeRequired⟩
  | strange => ⟨strange, schemeParameter, bridgeRequired⟩
  | charm => ⟨charm, schemeParameter, bridgeRequired⟩
  | bottom => ⟨bottom, schemeParameter, bridgeRequired⟩
  | neutrinoAbs => ⟨neutrinoAbs, differenceOnly, ratioOnly⟩
  | proton => ⟨proton, compositeBinding, bindingRequired⟩

/-- The canonical observable-first table. -/
def observableRows : List ObservableMassRow :=
  [ rowOf electron
  , rowOf muon
  , rowOf tau
  , rowOf zBoson
  , rowOf higgs
  , rowOf wBoson
  , rowOf top
  , rowOf up
  , rowOf down
  , rowOf strange
  , rowOf charm
  , rowOf bottom
  , rowOf neutrinoAbs
  , rowOf proton ]

/-- A row can be used as a direct mass-value test only for direct or resonance
observables that do not require a separate display theorem. -/
def directMassValueCheckAllowed (r : ObservableMassRow) : Bool :=
  match r.target, r.verdict with
  | directObservable, directCheck => true
  | resonanceObservable, directCheck => true
  | _, _ => false

/-- A row is blocked because it is a Standard Model scheme parameter. -/
def schemeBridgeRequired (r : ObservableMassRow) : Bool :=
  match r.target, r.verdict with
  | ComparisonTarget.schemeParameter, bridgeRequired => true
  | _, _ => false

/-- A row is blocked because only differences/ratios are observed. -/
def ratioOnlyRequired (r : ObservableMassRow) : Bool :=
  match r.target, r.verdict with
  | ComparisonTarget.differenceOnly, ratioOnly => true
  | _, _ => false

/-- A row requires a composite binding operator rather than a fundamental mass bridge. -/
def bindingRequired (r : ObservableMassRow) : Bool :=
  match r.target, r.verdict with
  | compositeBinding, ComparisonVerdict.bindingRequired => true
  | _, _ => false

/-! ## Theorems enforcing the comparison discipline -/

theorem observableRows_size : observableRows.length = 14 := by decide

theorem electron_row_direct :
    directMassValueCheckAllowed (rowOf electron) = true := by
  decide

theorem z_row_direct :
    directMassValueCheckAllowed (rowOf zBoson) = true := by
  decide

theorem w_row_not_direct :
    directMassValueCheckAllowed (rowOf wBoson) = false := by
  decide

theorem top_row_not_direct :
    directMassValueCheckAllowed (rowOf top) = false := by
  decide

theorem confined_quark_rows_require_bridge :
    [up, down, strange, charm, bottom].all
      (fun p => schemeBridgeRequired (rowOf p)) = true := by
  decide

theorem confined_quark_rows_not_direct_mass_checks :
    [up, down, strange, charm, bottom].all
      (fun p => !directMassValueCheckAllowed (rowOf p)) = true := by
  decide

theorem absolute_neutrino_ratio_only :
    ratioOnlyRequired (rowOf neutrinoAbs) = true ∧
      directMassValueCheckAllowed (rowOf neutrinoAbs) = false := by
  decide

theorem proton_requires_binding_operator :
    bindingRequired (rowOf proton) = true ∧
      directMassValueCheckAllowed (rowOf proton) = false := by
  decide

/-- The observable-first classification agrees with the independent
`MassEpistemics` registry on the two most dangerous confusions: quarks are scheme
parameters, and the absolute neutrino row is difference-only. -/
theorem agrees_with_mass_epistemics_on_blockers :
    MassEpistemics.confinedQuarks.all
      (fun p => schemeBridgeRequired (rowOf p)) = true ∧
    ratioOnlyRequired (rowOf neutrinoAbs) = true := by
  decide

/-! ## Reused numerical certificates on rows where direct comparison is allowed -/

/-- Existing charged-lepton scorecard certificate, now explicitly attached only
to observable rows rather than to scheme-parameter rows. -/
theorem charged_lepton_scorecard_available :
    Nonempty ChargedLeptonMassScoreCard.ChargedLeptonMassScoreCardCert :=
  ChargedLeptonMassScoreCard.chargedLeptonMassScoreCardCert_holds

/-- Existing Z scorecard certificate, a resonance row with direct comparison
allowed by this taxonomy. -/
noncomputable def z_scorecard_available :
    ZBosonMassScoreCard.ZBosonMassScoreCardCert :=
  ZBosonMassScoreCard.zBosonMassScoreCardCert_holds

/-- Existing quark ratio/algebra certificate, but with the absolute bridge still
named rather than promoted to a direct PDG mass claim. -/
theorem quark_absolute_bridge_certificate_available :
    Nonempty QuarkAbsoluteBridgeScoreCard.QuarkAbsoluteBridgeScoreCardCert :=
  QuarkAbsoluteBridgeScoreCard.quarkAbsoluteBridgeScoreCardCert_holds

/-- Existing neutral-sector structural certificate. The observable scorecard
permits ratio/order comparison, not an absolute mass comparison. -/
noncomputable def neutrino_majorana_certificate_available :
    NeutrinoMajoranaLadder.NeutrinoMajoranaCert :=
  NeutrinoMajoranaLadder.neutrinoMajoranaCert_holds

/-! ## Master certificate -/

/-- The first closure artifact from the total plan: every row has an observable
classification, direct rows can carry existing scorecards, and the two main
false-comparison modes (quark scheme masses, absolute neutrino masses) are
machine-blocked. -/
structure ObservableMassScorecardCert : Prop where
  table_size : observableRows.length = 14
  electron_direct : directMassValueCheckAllowed (rowOf electron) = true
  z_direct : directMassValueCheckAllowed (rowOf zBoson) = true
  quarks_need_bridge :
    [up, down, strange, charm, bottom].all
      (fun p => schemeBridgeRequired (rowOf p)) = true
  quarks_not_direct :
    [up, down, strange, charm, bottom].all
      (fun p => !directMassValueCheckAllowed (rowOf p)) = true
  neutrino_ratio_only :
    ratioOnlyRequired (rowOf neutrinoAbs) = true ∧
      directMassValueCheckAllowed (rowOf neutrinoAbs) = false
  proton_binding :
    bindingRequired (rowOf proton) = true ∧
      directMassValueCheckAllowed (rowOf proton) = false
  epistemics_agree :
    MassEpistemics.confinedQuarks.all
      (fun p => schemeBridgeRequired (rowOf p)) = true ∧
    ratioOnlyRequired (rowOf neutrinoAbs) = true

/-- The observable-first scorecard certificate holds. -/
def observableMassScorecardCert : ObservableMassScorecardCert where
  table_size := observableRows_size
  electron_direct := electron_row_direct
  z_direct := z_row_direct
  quarks_need_bridge := confined_quark_rows_require_bridge
  quarks_not_direct := confined_quark_rows_not_direct_mass_checks
  neutrino_ratio_only := absolute_neutrino_ratio_only
  proton_binding := proton_requires_binding_operator
  epistemics_agree := agrees_with_mass_epistemics_on_blockers

end ObservableMassScorecard
end Masses
end IndisputableMonolith

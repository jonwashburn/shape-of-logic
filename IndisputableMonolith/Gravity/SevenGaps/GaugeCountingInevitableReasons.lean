import IndisputableMonolith.Gravity.SevenGaps.MeasureSubstrateBlocker
import IndisputableMonolith.Gravity.SevenGaps.MeasureInvarianceNoGo
import IndisputableMonolith.Gravity.SevenGaps.Gap2PostingLayerFloor
import IndisputableMonolith.Gravity.SevenGaps.Gap2GaugeVolume
import IndisputableMonolith.Gravity.SevenGaps.Gap2LabelInsertionDynamics
import IndisputableMonolith.Gravity.SevenGaps.Gap2GluingLawStationarity
import IndisputableMonolith.Gravity.SevenGaps.Gap2FugacityPostingGluing
import IndisputableMonolith.Gravity.SevenGaps.Gap2SizeBlindnessReach
import IndisputableMonolith.Gravity.SevenGaps.Gap2LedgerSiteBlindness
import IndisputableMonolith.Gravity.Analysis.RecognitionDualEntryEnrichment4D

/-!
# Gauge-counting inevitable reasons (necessary-reasons census)

Assume the Gap-2 measure target is required: richer RecognitionLedger /
posting-layer structure forces
`MeasureSubstrateBlocker.GaugeCountingPrinciple` for the physical class
mass (equivalently `ν = 1/|Aut|`). Then every fact that would make that
unavoidable is listed below. Each reason is proved, left OPEN, recorded
as MODEL, or refuted. A failed reason does not automatically mean its
opposite: it forces a corrected floor plan.

Method: `plans/Necessary_Reasons_Process_20260807.html`.
Exemplar shape: `OneCarrierInevitableReasons.lean`.
Binding prompt:
`plans/QG_Gap2_GaugeCounting_Necessary_Reasons_Session_Prompt_20260807.txt`.

Honesty:

* THEOREM: invariance underdetermines the measure; GCP ↔ gaugeOrbitMass;
  gaugeOrbitMass satisfies GCP; uniform class mass fails GCP; pinned
  carrier collapses to complex counting; uniqueness wall for invariant
  enrichments; equivariant costs contribute no factor; label-asymmetric
  letter costs exist; orbit-stabilizer accounting; mere label-indifference
  does not select Gibbs.
* THEOREM (R18 block): the fugacity–action rebooking gauge
  `(a, S) ↦ (t·a, S + log t)` preserves the Boltzmann product pointwise;
  every satisfiable rebooking-invariant prior admits a non-unit-fugacity
  representative, so none can select `a ≡ 1`; every product-visible prior
  (one that sees only the physical weight) is rebooking-invariant.
* REFUTED as a derivation of GCP from richer structure: invariant
  enrichment, equivariant posting cost, bare-posting gluing, unit fugacity
  from posting+gluing, size-blindness from cluster decomposition,
  disjoint-union factorization, ledger-cost readout, vertex-site symmetry
  count, and “label indifference” as a selecting principle.
* REFUTED (scoped, R18): no prior that sees only the physical Boltzmann
  product forces the Gibbs numerator `a ≡ 1`. The literal
  `AssumedRequired` Prop is vacuously inhabitable (`R18_vacuity_guard`
  scores that decoy); the honest discharge is the wall, not the
  inhabitant.
* OPEN residual: an action-first prior. The only selectors outside the
  wall pin the action independently of the measure: derive the ledger
  action (the posting schedule nature executes) first, then the fugacity
  booking is a convention and GCP for the counting measure is R03. Child
  census rows U12 (derive `GluingLaw`) and U13 (justified asymmetry) in
  `UnitFugacitySelector.lean` are the typed sub-lanes.
* No inhabitation of “ledger forces GCP” is claimed. The corrected target
  is typed below.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace GaugeCountingInevitableReasons

open PathSumMeasure ExactShellGaugePreflight
open MeasureSubstrateBlocker MeasureInvarianceNoGo
open Gap2PostingLayerFloor Gap2GaugeVolume Gap2PostingCostDerivation
open GaugeHistoryMeasure
open Gap2LabelInsertionDynamics Gap2GluingLawStationarity
open Gap2FugacityPostingGluing Gap2SizeBlindnessReach Gap2GluingDerivation
open Gap2LedgerSiteBlindness
open IndisputableMonolith.Gravity.RecognitionLedger
open Analysis.RecognitionDualEntryEnrichment4D

noncomputable section

/-! ## Reason census

R01 invariance axioms underdetermine the path-sum measure
R02 GaugeCountingPrinciple ↔ ν = gaugeOrbitMass
R03 gaugeOrbitMass satisfies GaugeCountingPrinciple
R04 uniform class mass fails GaugeCountingPrinciple
R05 pinned CanonicalHistory count equals complex count
R06 state-factored weights collapse on the pinned carrier
R07 among invariant labeled weights, GCP forces Gibbs (uniqueness wall)
R08 equivariant posting costs contribute no measure factor
R09 label-asymmetric letter costs exist
R10 mere label-indifference does not select Gibbs
R11 orbit-stabilizer accounting is theorem (label count = orbit × |Aut|)
R12 bare fixed-carrier posting moves do not derive the gluing factor
R13 posting structure plus gluing does not force unit fugacity
R14 cluster decomposition does not derive size-blindness as stated
R15 disjoint-union multiplicativity does not force the class weight
R16 recognition ledger cost values do not read out the class measure
R17 Fin-2 vertex-site symmetry count cannot supply Aut-sensitive mass
R18 Gibbs numerator a ≡ 1 is forced by a prior principle / schedule
-/

/-- Status table for the reason census. -/
structure ReasonStatus where
  id : String
  title : String
  /-- `"THEOREM"`, `"OPEN"`, `"MODEL"`, or `"REFUTED"`. -/
  status : String

def reasonTable : List ReasonStatus :=
  [ ⟨"R01", "invariance axioms underdetermine the measure", "THEOREM"⟩
  , ⟨"R02", "GCP iff ν equals gaugeOrbitMass", "THEOREM"⟩
  , ⟨"R03", "gaugeOrbitMass satisfies GCP", "THEOREM"⟩
  , ⟨"R04", "uniform class mass fails GCP", "THEOREM"⟩
  , ⟨"R05", "pinned history count equals complex count", "THEOREM"⟩
  , ⟨"R06", "pinned state-factored weights are complex functions", "THEOREM"⟩
  , ⟨"R07", "invariant enrichment unique Gibbs / cannot derive GCP", "REFUTED"⟩
  , ⟨"R08", "equivariant cost contributes no measure factor", "REFUTED"⟩
  , ⟨"R09", "label-asymmetric letter costs exist", "THEOREM"⟩
  , ⟨"R10", "mere label-indifference does not select Gibbs", "REFUTED"⟩
  , ⟨"R11", "orbit-stabilizer accounting is theorem", "THEOREM"⟩
  , ⟨"R12", "bare posting does not derive gluing", "REFUTED"⟩
  , ⟨"R13", "posting+gluing does not force unit fugacity", "REFUTED"⟩
  , ⟨"R14", "cluster decomposition does not give size-blindness", "REFUTED"⟩
  , ⟨"R15", "disjoint-union factorization does not force class weight", "REFUTED"⟩
  , ⟨"R16", "ledger cost values do not read class measure", "REFUTED"⟩
  , ⟨"R17", "Fin-2 site-symmetry count is Aut-blind", "REFUTED"⟩
  , ⟨"R18", "no rebooking-invariant (incl. product-visible) prior forces a≡1", "REFUTED"⟩ ]

theorem reasonTable_length : reasonTable.length = 18 := by
  decide

/-! ## Already THEOREM reasons (imported and re-stood) -/

/-- **R01.** Invariance alone underdetermines the path-sum measure. -/
theorem R01_invariance_underdetermines (B : ℕ) (hB : 2 ≤ B) :
    ∃ w₁ w₂ : BoundedComplex B → ℝ,
      InvarianceAxioms B w₁ ∧ InvarianceAxioms B w₂ ∧ w₁ ≠ w₂ :=
  invariance_underdetermines_measure B hB

/-- **R02.** Normalized gauge counting selects exactly the counting mass. -/
theorem R02_gcp_iff_gaugeOrbitMass {B : ℕ} (ν : TriangulationClass B → ℝ) :
    GaugeCountingPrinciple ν ↔ ν = gaugeOrbitMass :=
  gaugeCountingPrinciple_iff_eq_gaugeOrbitMass ν

/-- **R03.** The counting-defined mass satisfies GCP. -/
theorem R03_gaugeOrbitMass_satisfies {B : ℕ} :
    GaugeCountingPrinciple (gaugeOrbitMass : TriangulationClass B → ℝ) :=
  gaugeOrbitMass_satisfies

/-- **R04.** The quotient-uniform decoy fails GCP. -/
theorem R04_uniform_fails (B : ℕ) (hB : 2 ≤ B) :
    ¬ GaugeCountingPrinciple
      (uniformClassMass : TriangulationClass B → ℝ) :=
  uniformClassMass_not_gaugeCounting B hB

/-- **R05.** On the pinned carrier, counting is complex counting. -/
theorem R05_pinned_count_is_complex (B : ℕ) :
    Nat.card (CanonicalHistory B) = Nat.card (BoundedComplex B) :=
  canonical_count_eq_complex_count B

/-- **R06.** State-factored weights collapse on the pinned carrier. -/
theorem R06_pinned_weights_are_complex {B : ℕ}
    (F : ∀ (K : BoundedComplex B), DualEntryStrainState (PostingAlphabet K) → ℝ) :
    ∃ g : BoundedComplex B → ℝ, ∀ CH : CanonicalHistory B,
      F CH.underlying CH.H.state = g CH.underlying :=
  state_factored_weight_is_complex_function F

/-- **R09.** Label-asymmetric letter costs exist. -/
theorem R09_label_asymmetric_exists : ∃ c : LetterCost, ¬ Equivariant c :=
  label_asymmetric_structure_exists

/-- **R11.** Orbit-stabilizer accounting is theorem, not premise. -/
theorem R11_orbit_stabilizer {B : ℕ} (K : BoundedComplex B) :
    gaugeOrbitCard K * Nat.card (Aut K)
      = K.nV.factorial * (K.nE.factorial * K.nT.factorial) :=
  irreducible_input_is_orbit_stabilizer K

/-! ## REFUTED derivation routes (richer structure → GCP) -/

/-- **R07 REFUTED as a derivation.** Among relabeling-invariant labeled
weights, GCP holds of the class mass iff the weight is Gibbs pointwise.
Asking for GCP among invariant enrichments leaves no degree of freedom:
the principle and the Gibbs premise are the same assumption stated twice. -/
theorem R07_invariant_enrichment_unique_gibbs (B : ℕ) (w : BoundedComplex B → ℝ)
    (hinv : ∀ K K', Equivalent K K' → w K = w K') :
    GaugeCountingPrinciple (classMass w) ↔
      ∀ K : BoundedComplex B, w K = gibbsWeight K :=
  invariant_enrichment_unique_gibbs B w hinv

/-- **R08 REFUTED as a derivation.** Equivariant letter costs post `mu`
exactly when their Boltzmann numerator is identically one. -/
theorem R08_equivariant_cost_no_factor {c : LetterCost} (hc : Equivariant c)
    (B : ℕ) :
    (∀ K : BoundedComplex B,
        classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K)
      ↔ ∀ K : BoundedComplex B, Real.exp (-(historyCost c B K)) = 1 :=
  equivariant_cost_contributes_no_factor hc B

/-- **R10 REFUTED as a selecting principle.** For any function `a` of the
three index sizes, the fugacity weight is relabeling-invariant, so an
entire family is label-indifferent. Indifference alone cannot select the
Gibbs weight `a ≡ 1`. Banked kill:
`N-route-gap2-premise-is-label-indifference`. -/
theorem R10_indifference_family_underdetermines {B : ℕ}
    (a : ℕ → ℕ → ℕ → ℝ) {K K' : BoundedComplex B}
    (h : Equivalent K K') :
    fugacityWeight a K = fugacityWeight a K' :=
  fugacityWeight_invariant a h

/-- **R10 companion.** GCP for a fugacity weight holds exactly when the
fugacity is one on occupied sectors: the undischarged selector is unit
cross-sector fugacity, not indifference. -/
theorem R10_gcp_iff_unit_fugacity {B : ℕ} (a : ℕ → ℕ → ℕ → ℝ) :
    GaugeCountingPrinciple (classMass (fugacityWeight a : BoundedComplex B → ℝ)) ↔
      ∀ K : BoundedComplex B, a K.nV K.nE K.nT = 1 :=
  gaugeCounting_iff_fugacity_one a

/-! ## Corrected floor plan (no automatic opposite) -/

/-- A failed reason does not license its opposite by default. -/
structure CorrectedFloorPlan where
  failedReason : String
  measurement : String
  correctedTarget : String
  doesNotKill : String

/-- Banked corrected floor plans from failed reasons. -/
def correctedFloorPlans : List CorrectedFloorPlan :=
  [ ⟨"R07",
      "among invariant labeled weights, GCP ↔ weight = gibbsWeight pointwise",
      "derive the Gibbs weight (or a≡1) from a prior principle, not from invariant enrichment of the complex",
      "orbit-stabilizer accounting, GCP↔1/|Aut|, or the counting mass itself"⟩
  , ⟨"R08",
      "equivariant costs post mu iff Boltzmann numerator is identically 1",
      "any cost-layer derivation must either force numerator 1 by a new premise or leave the equivariant class",
      "non-equivariant / label-asymmetric letter costs (R09 inhabited)"⟩
  , ⟨"R10",
      "every a(sizes)/(nV!nE!nT!) is label-indifferent, so indifference admits a family",
      "force the Gibbs numerator a≡1 among that family (or an equivalent selecting law)",
      "the statement that GCP equals label-density / 1/|Aut| once Gibbs is chosen"⟩
  , ⟨"assumed target",
      "posting_layer_floor: pinned carrier + uniqueness wall exclude richer invariant derivation of GCP",
      "CorrectedMeasurePremise: force Gibbs numerator a≡1 from a named prior stronger than indifference, or from justified label-asymmetric structure, or from the posting schedule nature executes",
      "GCP as a typed obligation, gaugeOrbitMass_satisfies, or mu = 1/|Aut| once Gibbs is selected"⟩
  , ⟨"R18",
      "every satisfiable rebooking-invariant prior admits a doubled-fugacity representative (t=2 gauge step at the two-point complex), and every product-visible prior is rebooking-invariant",
      "action-first: derive the ledger action independently of the measure, then the fugacity booking is a convention and GCP holds of the counting measure by R03",
      "the child-census lanes U12 (derive GluingLaw) and U13 (justified asymmetry), or any prior that pins the action rather than the measure"⟩ ]

theorem correctedFloorPlans_length : correctedFloorPlans.length = 5 := by
  decide

/-- **Corrected measure premise (typed, not inhabited).** The surviving
obligation after the reason audit: select the Gibbs numerator `a ≡ 1`
among the indifference family, by a named principle stronger than
relabeling indifference. -/
structure CorrectedMeasurePremise where
  /-- Named prior that forces the Boltzmann numerator to be identically one
  (equivalently selects gibbsWeight among size-dependent indifference
  weights). -/
  selectsGibbsNumerator : Prop
  /-- That prior is not mere relabeling invariance / label indifference. -/
  strongerThanIndifference : Prop
  /-- From the prior, GaugeCountingPrinciple holds of the physical class mass. -/
  forcesGCP : Prop

/-- Room C's assumed-required target.

The proposition records the surviving obligation: some ledger fact stronger
than label indifference must select the Gibbs numerator and force
`GaugeCountingPrinciple`. It is a target package, not an inhabitant. -/
def AssumedRequired : Prop :=
  ∃ p : CorrectedMeasurePremise,
    p.selectsGibbsNumerator ∧
      p.strongerThanIndifference ∧ p.forcesGCP

/-- The assumed target “richer ledger structure forces GCP” is not claimed.
The corrected obligation is the uninhabited `CorrectedMeasurePremise`. -/
def assumedTargetStatus : String := "REFUTED_AS_STATED"

/-! ## Numbered reason Props -/

def R01 : Prop :=
  ∀ (B : ℕ), 2 ≤ B →
    ∃ w₁ w₂ : BoundedComplex B → ℝ,
      InvarianceAxioms B w₁ ∧ InvarianceAxioms B w₂ ∧ w₁ ≠ w₂

def R02 : Prop :=
  ∀ {B : ℕ} (ν : TriangulationClass B → ℝ),
    GaugeCountingPrinciple ν ↔ ν = gaugeOrbitMass

def R03 : Prop :=
  ∀ (B : ℕ),
    GaugeCountingPrinciple (gaugeOrbitMass : TriangulationClass B → ℝ)

def R04 : Prop :=
  ∀ (B : ℕ), 2 ≤ B →
    ¬ GaugeCountingPrinciple
      (uniformClassMass : TriangulationClass B → ℝ)

def R05 : Prop :=
  ∀ (B : ℕ),
    Nat.card (CanonicalHistory B) = Nat.card (BoundedComplex B)

def R06 : Prop :=
  ∀ {B : ℕ}
    (F : ∀ (K : BoundedComplex B),
      DualEntryStrainState (PostingAlphabet K) → ℝ),
    ∃ g : BoundedComplex B → ℝ,
      ∀ CH : CanonicalHistory B,
        F CH.underlying CH.H.state = g CH.underlying

def R07 : Prop :=
  ∀ (B : ℕ) (w : BoundedComplex B → ℝ),
    (∀ K K', Equivalent K K' → w K = w K') →
      (GaugeCountingPrinciple (classMass w) ↔
        ∀ K : BoundedComplex B, w K = gibbsWeight K)

def R08 : Prop :=
  ∀ {c : LetterCost}, Equivariant c → ∀ (B : ℕ),
    (∀ K : BoundedComplex B,
        classMass (postedWeight c B) (Quotient.mk (relabelSetoid B) K) = mu K)
      ↔ ∀ K : BoundedComplex B, Real.exp (-(historyCost c B K)) = 1

def R09 : Prop := ∃ c : LetterCost, ¬ Equivariant c

def R10 : Prop :=
  ∀ {B : ℕ} (a : ℕ → ℕ → ℕ → ℝ)
    {K K' : BoundedComplex B}, Equivalent K K' →
      fugacityWeight a K = fugacityWeight a K'

def R11 : Prop :=
  ∀ {B : ℕ} (K : BoundedComplex B),
    gaugeOrbitCard K * Nat.card (Aut K)
      = K.nV.factorial * (K.nE.factorial * K.nT.factorial)

/-- R12 is the imported bare-posting-to-gluing no-go. -/
def R12 : Prop :=
  InsertionStationarity factorialWorld.weight ∧
    ¬ InsertionStationarity constantWorld.weight ∧
    (∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ]
      (L₁ L₂ : Recognition.Ledger (discreteCarrier Λ)),
      WorldReachable factorialWorld L₁ L₂ ↔
        WorldReachable constantWorld L₁ L₂)

def R13 : Prop :=
  ∀ {u v w : ℝ}, 0 < u → 0 < v → 0 < w →
    ¬ (u = 1 ∧ v = 1 ∧ w = 1) →
      ∃ (c : LetterCost) (f : ℕ → ℕ → ℕ → ℝ),
        KindOnly c ∧ Equivariant c ∧ SizeBlind (postedWeight c)
          ∧ (∀ (B' : ℕ) (K : BoundedComplex B'),
              postedWeight c B' K = sizeWeight f K)
          ∧ CarrierShuffle f
          ∧ ¬ UnitFugacity f

def R14 : Prop :=
  ∀ {lam : ℝ}, 0 < lam → lam ≠ 1 →
    SatisfiesTheOtherHypotheses (statWeight properStat lam)
      ∧ ¬ SizeBlind (statWeight properStat lam)
      ∧ classMass (statWeight properStat lam 2)
          (Quotient.mk (relabelSetoid 2) twoBridges)
          ≠ mu twoBridges

/-- R15 is the imported disjoint-union gluing counterexample. -/
def R15 : Prop :=
  GluesGenerally (fun B => (uniformWeight : BoundedComplex B → ℝ)) ∧
    classMass uniformWeight
        (Quotient.mk (relabelSetoid (1 + 2 + 0)) (bouquet 2 0)) ≠
      mu (bouquet 2 0)

def R16 : Prop :=
  ∀ (f : BoundedComplex 2 → ℝ), (∀ K, 0 ≤ f K) →
    ∃ enc : BoundedComplex 2 → RecognitionLedger (Fin 2),
      ∀ K, (enc K).cost 0 1 = f K

def R17 : Prop :=
  ∀ (enc : BoundedComplex 2 → RecognitionLedger (Fin 2))
    (g : ℕ → ℝ) (ν : TriangulationClass 2 → ℝ),
    (∀ K : BoundedComplex 2, K.nV = 2 →
      ν (Quotient.mk (relabelSetoid 2) K) =
        g (siteSymCard (enc K))) →
      ¬ GaugeCountingPrinciple ν

/-- R18 is the surviving selector target. OPEN. -/
def R18 : Prop := AssumedRequired

/-! ## Banked reason rows -/

theorem R01_reason : R01 := by
  intro B hB
  exact R01_invariance_underdetermines B hB

theorem R02_reason : R02 := by
  intro B ν
  exact R02_gcp_iff_gaugeOrbitMass ν

theorem R03_reason : R03 := by
  intro B
  exact R03_gaugeOrbitMass_satisfies

theorem R04_reason : R04 := by
  intro B hB
  exact R04_uniform_fails B hB

theorem R05_reason : R05 := by
  intro B
  exact R05_pinned_count_is_complex B

theorem R06_reason : R06 := by
  intro B F
  exact R06_pinned_weights_are_complex F

theorem R07_reason : R07 :=
  fun B w hinv => R07_invariant_enrichment_unique_gibbs B w hinv

theorem R08_reason : R08 := by
  intro c hc B
  exact R08_equivariant_cost_no_factor hc B

theorem R09_reason : R09 :=
  R09_label_asymmetric_exists

theorem R10_reason : R10 := by
  intro B a K K' h
  exact R10_indifference_family_underdetermines a h

theorem R11_reason : R11 := by
  intro B K
  exact R11_orbit_stabilizer K

theorem R12_refuted : R12 :=
  Gap2GluingLawStationarity.bare_posting_does_not_force_insertion_stationarity

theorem R13_refuted : R13 := by
  intro u v w hu hv hw hne
  exact gluing_and_posting_do_not_force_unit_fugacity hu hv hw hne

theorem R14_refuted : R14 :=
  size_blindness_not_forced_by_the_other_hypotheses

theorem R15_refuted : R15 :=
  gluing_alone_does_not_force_mu

theorem R16_refuted : R16 := by
  intro f hf
  exact encoding_unconstrained f hf

theorem R17_refuted : R17 := by
  intro enc g ν hfactor
  exact no_siteSymmetry_measure (hB := by norm_num) (hB1 := by norm_num)
    enc g ν hfactor

/-! ## R18: the booking-gauge wall (scoped refutation from survivors)

The survivors R01–R17 leave one question: can any prior principle force the
Gibbs numerator `a ≡ 1`? The absorption identity U07
(`fugacity_absorbs_into_action`) is sharpened here into the obstruction.
The split of the physical Boltzmann product into a sector fugacity and an
action is a bookkeeping symmetry: `(a, S) ↦ (t·a, S + log t)` preserves the
product pointwise (`R18_rebooking_preserves_product`). A prior that
respects that symmetry, and in particular one that sees only the physical
product weight (`ProductVisible`), cannot select `a ≡ 1`
(`R18_no_rebooking_invariant_selector`, `R18_no_product_visible_selector`):
if it is satisfiable at all, it admits a representative whose fugacity is
not one (`R18_rebooking_invariant_admits_nonunit`).

The literal `R18` Prop is also vacuously inhabitable, because
`CorrectedMeasurePremise` packages three uninterpreted Props;
`R18_vacuity_guard` records the trivial inhabitant so the row can never be
scored by inhabiting the package. The honest content of the row is the
wall.

Survivor, with no automatic opposite: a prior outside the wall must pin the
action independently of the measure. Derive the ledger action first; the
fugacity booking is then a convention, and GCP for the counting measure is
R03. That is the action-first lane, with the child census rows U12 (derive
`GluingLaw`) and U13 (justified asymmetry) still open in
`UnitFugacitySelector.lean`. -/

/-- The rebooking gauge transformation preserves the physical Boltzmann
product: scaling the sector fugacity by a positive `t` while shifting the
action by `log t` leaves `fugacityWeight · exp(-S)` pointwise unchanged.
This is the general step of which U07 (`fugacity_absorbs_into_action`) is
the total-absorption case `t = 1/a`. -/
theorem R18_rebooking_preserves_product {B : ℕ}
    (a a' : ℕ → ℕ → ℕ → ℝ) (t : ℝ) (S : BoundedComplex B → ℝ)
    (K : BoundedComplex B)
    (ht : 0 < t) (ha' : a' K.nV K.nE K.nT = t * a K.nV K.nE K.nT) :
    fugacityWeight a' K * Real.exp (-(S K + Real.log t))
      = fugacityWeight a K * Real.exp (-(S K)) := by
  unfold fugacityWeight
  rw [ha', neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg (Real.log t),
    Real.exp_log ht]
  have ht0 : (t : ℝ) ≠ 0 := ht.ne'
  have hE0 : Real.exp (S K) ≠ 0 := Real.exp_ne_zero (S K)
  have hV0 :
      ((Nat.factorial K.nV * (Nat.factorial K.nE * Nat.factorial K.nT) : ℕ) : ℝ)
        ≠ 0 := by
    have hpos : 0 < Nat.factorial K.nV
        * (Nat.factorial K.nE * Nat.factorial K.nT) :=
      Nat.mul_pos (Nat.factorial_pos _)
        (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
    exact_mod_cast hpos.ne'
  field_simp

/-- **Rebooking invariance**: a prior on (fugacity, action) presentations
respects the bookkeeping gauge. The doubling step suffices: it generates
the contradiction at the two-point complex. -/
def RebookingInvariant {B : ℕ}
    (P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop) : Prop :=
  ∀ (a : ℕ → ℕ → ℕ → ℝ) (S : BoundedComplex B → ℝ),
    P a S → P (fun nV nE nT => 2 * a nV nE nT) (fun K => S K + Real.log 2)

/-- **R18 wall, counterexample form.** A satisfiable rebooking-invariant
prior always admits a presentation whose sector fugacity is not identically
one on occupied complexes: double the fugacity and absorb `log 2` into the
action. The non-unit value is witnessed at the two-point complex. -/
theorem R18_rebooking_invariant_admits_nonunit {B : ℕ} (hB : 2 ≤ B)
    (P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop)
    (hgauge : RebookingInvariant P)
    (a₀ : ℕ → ℕ → ℕ → ℝ) (S₀ : BoundedComplex B → ℝ) (h₀ : P a₀ S₀) :
    ∃ (a : ℕ → ℕ → ℕ → ℝ) (S : BoundedComplex B → ℝ),
      P a S ∧ ∃ K : BoundedComplex B, a K.nV K.nE K.nT ≠ 1 := by
  by_cases h : a₀ 2 0 0 = 1
  · refine ⟨fun nV nE nT => 2 * a₀ nV nE nT, fun K => S₀ K + Real.log 2,
      hgauge a₀ S₀ h₀, MeasureInvarianceNoGo.twoPointComplex B hB, ?_⟩
    show (2 : ℝ) * a₀ 2 0 0 ≠ 1
    rw [h]
    norm_num
  · exact ⟨a₀, S₀, h₀, MeasureInvarianceNoGo.twoPointComplex B hB, h⟩

/-- **R18 wall, selector-impossibility form.** No satisfiable
rebooking-invariant prior forces the Gibbs numerator: if `P` held only of
presentations with unit fugacity on occupied complexes, the doubled
presentation would contradict the unit value at the two-point complex. -/
theorem R18_no_rebooking_invariant_selector {B : ℕ} (hB : 2 ≤ B)
    (P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop)
    (hgauge : RebookingInvariant P)
    (hsel : ∀ (a : ℕ → ℕ → ℕ → ℝ) (S : BoundedComplex B → ℝ),
      P a S → ∀ K : BoundedComplex B, a K.nV K.nE K.nT = 1)
    (a₀ : ℕ → ℕ → ℕ → ℝ) (S₀ : BoundedComplex B → ℝ) (h₀ : P a₀ S₀) :
    False := by
  have h1 : a₀ 2 0 0 = 1 :=
    hsel a₀ S₀ h₀ (MeasureInvarianceNoGo.twoPointComplex B hB)
  have h2 : (2 : ℝ) * a₀ 2 0 0 = 1 :=
    hsel _ _ (hgauge a₀ S₀ h₀) (MeasureInvarianceNoGo.twoPointComplex B hB)
  rw [h1] at h2
  norm_num at h2

/-- **Product-visible priors**: those that ask about the physical Boltzmann
product only. Ledger-internal candidate priors (label indifference of the
weight, gluing of the product, insertion stationarity of the product, orbit
accounting) all have this form, because their inputs are functions of the
product. -/
def ProductVisible {B : ℕ}
    (P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop) : Prop :=
  ∃ Q : (BoundedComplex B → ℝ) → Prop,
    ∀ (a : ℕ → ℕ → ℕ → ℝ) (S : BoundedComplex B → ℝ),
      P a S ↔ Q (fun K => fugacityWeight a K * Real.exp (-(S K)))

/-- Every product-visible prior is rebooking-invariant: the gauge step
preserves the product pointwise. -/
theorem R18_product_visible_is_rebooking_invariant {B : ℕ}
    {P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop}
    (hP : ProductVisible P) : RebookingInvariant P := by
  obtain ⟨Q, hQ⟩ := hP
  intro a S h
  rw [hQ] at h ⊢
  have hpt : (fun K : BoundedComplex B =>
        fugacityWeight (fun nV nE nT => 2 * a nV nE nT) K *
          Real.exp (-(S K + Real.log 2)))
      = (fun K : BoundedComplex B =>
        fugacityWeight a K * Real.exp (-(S K))) := by
    funext K
    exact R18_rebooking_preserves_product a (fun nV nE nT => 2 * a nV nE nT)
      2 S K (by norm_num) rfl
  rw [hpt]
  exact h

/-- **R18 wall, ledger-internal corollary.** No satisfiable product-visible
prior forces the Gibbs numerator. -/
theorem R18_no_product_visible_selector {B : ℕ} (hB : 2 ≤ B)
    (P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop)
    (hP : ProductVisible P)
    (hsel : ∀ (a : ℕ → ℕ → ℕ → ℝ) (S : BoundedComplex B → ℝ),
      P a S → ∀ K : BoundedComplex B, a K.nV K.nE K.nT = 1)
    (a₀ : ℕ → ℕ → ℕ → ℝ) (S₀ : BoundedComplex B → ℝ) (h₀ : P a₀ S₀) :
    False :=
  R18_no_rebooking_invariant_selector hB P
    (R18_product_visible_is_rebooking_invariant hP) hsel a₀ S₀ h₀

/-- The R18 killing measurement, typed: over every cap with a two-point
complex, no satisfiable rebooking-invariant prior selects unit fugacity,
and the product-visible class sits inside the rebooking-invariant class. -/
def R18Wall : Prop :=
  ∀ (B : ℕ), 2 ≤ B →
    (∀ (P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop),
      RebookingInvariant P →
        (∀ (a : ℕ → ℕ → ℕ → ℝ) (S : BoundedComplex B → ℝ),
          P a S → ∀ K : BoundedComplex B, a K.nV K.nE K.nT = 1) →
        ∀ (a₀ : ℕ → ℕ → ℕ → ℝ) (S₀ : BoundedComplex B → ℝ),
          P a₀ S₀ → False)
    ∧ (∀ (P : (ℕ → ℕ → ℕ → ℝ) → (BoundedComplex B → ℝ) → Prop),
        ProductVisible P → RebookingInvariant P)

/-- **R18 REFUTED (scoped).** The Gibbs numerator is not forcible by any
prior invariant under the fugacity–action booking gauge, and every prior
that sees only the physical product weight is such a prior. -/
theorem R18_refuted : R18Wall := by
  intro B hB
  exact ⟨fun P hgauge hsel a₀ S₀ h₀ =>
      R18_no_rebooking_invariant_selector hB P hgauge hsel a₀ S₀ h₀,
    fun P hP => R18_product_visible_is_rebooking_invariant hP⟩

/-- **Vacuity guard (decoy scored).** The literal `R18` Prop is inhabitable
with zero content, because `CorrectedMeasurePremise` packages three
uninterpreted Props. This trivial inhabitant is recorded so the row can
never be scored by inhabiting the package: the honest discharge of R18 is
the wall `R18_refuted` plus the named survivor, never this witness. -/
theorem R18_vacuity_guard : R18 :=
  ⟨⟨True, True, True⟩, True.intro, True.intro, True.intro⟩

/-- R18 row verdict. -/
def R18Status : String := "REFUTED_OVER_REBOOKING_INVARIANT_PRIORS"

/-- First attack block on the corrected target (historical; R18 closed as
a scoped wall, so the block is superseded by `secondAttackBlock`). -/
def firstAttackBlock : List String :=
  ["R18", "R09", "R10", "R07", "R11"]

theorem firstAttackBlock_length : firstAttackBlock.length = 5 := by
  decide

/-- Second attack block on the twice-corrected target (historical; all
three rows resolved in the child census `UnitFugacitySelector` on
2026-08-07). The only priors outside the R18 wall pin the action
independently of the measure, so the surviving obligation was
action-first: derive the ledger cost the substrate posts, with the
fugacity booking then a convention and GCP given by R03. The child census
rows U12 (derive `GluingLaw`) and U13 (justified asymmetry) were the
typed sub-lanes. -/
def secondAttackBlock : List String :=
  ["ACTION-FIRST ledger cost derivation", "U12", "U13"]

theorem secondAttackBlock_length : secondAttackBlock.length = 3 := by
  decide

/-- Third attack block (2026-08-07 fifth pass). The child census resolved
the second block: U13 is REFUTED (scoped, no product-visible cost prior
selects unit fugacity), and U12 is THEOREM (the ledger-counted global
balance forces detailed balance on the birth-death chain, which forces
the inverse-factorial gluing law; see
`UnitFugacitySelector.globalBalance_forces_detailedBalance` and
`equilibrium_forces_gluingLaw`). The corrected measure premise is now
contentfully inhabited by the child's `equilibriumPrior`
(`U14_assumedRequired_inhabited`), superseding the `True`-package decoy
this file pre-scored in `R18_vacuity_guard`. What survives of
  "action-first" is exactly one organ: derive the equilibrium premise
itself (the physical weight IS a stationary state of the ledger-counted
recognition dynamics) from recognition law, the child's U15. The chain
is forced and the late-time state is its unique output; under the
parameter-free identification rule (2026-08-08) that reading is adopted
as MODEL in `UnitFugacitySelector.U15_identification_adopted`. -/
def thirdAttackBlock : List String := []

theorem thirdAttackBlock_length : thirdAttackBlock.length = 0 := by
  decide

/-- Public name for the next necessary-reasons block. -/
def nextAttackBlock : List String := thirdAttackBlock

theorem nextAttackBlock_length : nextAttackBlock.length = 0 := by
  decide

/-- R18 block receipt: the wall is theorem, the literal target is vacuously
inhabitable with the decoy scored, and the bookkeeping syncs. -/
theorem R18_block_certified :
    R18Wall ∧ R18 ∧ correctedFloorPlans.length = 5 ∧
      nextAttackBlock.length = 0 ∧
      R18Status = "REFUTED_OVER_REBOOKING_INVARIANT_PRIORS" :=
  ⟨R18_refuted, R18_vacuity_guard, correctedFloorPlans_length,
    nextAttackBlock_length, rfl⟩

/-- The existing corrected floor plan is also exposed as the requested stub
surface for later rows. -/
def correctedFloorPlansStub : List CorrectedFloorPlan :=
  correctedFloorPlans

theorem correctedFloorPlansStub_length :
    correctedFloorPlansStub.length = 5 := by
  decide

/- There is intentionally no composite certificate here. The banked rows
remain individually inspectable, and `AssumedRequired` is not closed: its
only inhabitant is the scored vacuity decoy `R18_vacuity_guard`. -/

end

#print axioms R18_rebooking_preserves_product
#print axioms R18_rebooking_invariant_admits_nonunit
#print axioms R18_no_rebooking_invariant_selector
#print axioms R18_product_visible_is_rebooking_invariant
#print axioms R18_no_product_visible_selector
#print axioms R18_refuted
#print axioms R18_vacuity_guard
#print axioms R18_block_certified

end GaugeCountingInevitableReasons
end SevenGaps
end Gravity
end IndisputableMonolith

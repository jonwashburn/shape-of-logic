import IndisputableMonolith.Foundation.PublicSpine.AxiomExtensionNecessityProbe
import IndisputableMonolith.Foundation.PublicSpine.CurrentRSBundle
import IndisputableMonolith.Foundation.PublicSpine.TangentChartCalibration
import IndisputableMonolith.Foundation.PublicSpine.PlasticVsAdjacencyMetered
import IndisputableMonolith.Foundation.PublicSpine.SeedOrbitPhase4Wall
import IndisputableMonolith.Foundation.PublicSpine.PostingPhase3Wall
import IndisputableMonolith.Foundation.PublicSpine.BooleanCompletePass
import IndisputableMonolith.Foundation.PublicSpine.ClockDischargeProbe

/-!
# PartINamedAxiomClosure

Four disclosed physical identifications close the Part I residuals: a
calibration law on the continuum cost, an adjacency law on the scale sequence,
a seed-orbit class law, and a semantic clock law.

* MODEL declarations prove consistency and nonvacuity.
* LAW structures state each physical identification.
* THEOREMS derive J, phi, seed composition, and the period bound from any law.

The laws are deliberately scoped. They do not universalize over the bare cost,
scale, orbit, or posting classes that contain the compiled countermodels; each
wall theorem below exhibits a member of the bare class that the law rejects.

## 2026-07-25: the four laws stopped being axioms

They were `axiom` declarations, which was strictly weaker than what this file
already proved, in two ways at once.

Logically the axioms added nothing. Each law type is proved inhabited here
(`calibrationLaw_nonempty` and its three siblings), so `Classical.choice`
already supplies a term of it, and an `axiom` whose type is a proved `Nonempty`
cannot exclude a model that the ambient theory did not already exclude. The
four cost an entry apiece in every downstream `#print axioms` footprint and
bought no strength for the price.

Mathematically they discarded generality. Every closure result below is proved
from the structure FIELDS alone and never from a property peculiar to a chosen
inhabitant, so each result holds of every law at once. Taking the law as an
explicit argument says that, and the old axiom-instantiated statement is
recovered by applying the theorem to any term of the type.

What the physical identification actually asserts is that the world's cost,
scale, orbit and posting discipline satisfy these four structures. That is an
empirical commitment. Carried as a hypothesis it arrives at every call site
where a reader can see it and a later theorem can discharge it, which is
exactly what a global axiom prevented.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace PartINamedAxiomClosure

open Cost.FunctionalEquation
open PrimitiveRecognitionCalculus.Calibration
open CostFromDistinction
open HierarchyForcing
open UnifiedForcingChain
open PhiForcingDerived
open Constants
open Patterns
open PerfectRecognition
open FreeJointRecognition
open TangentChartCalibration
open PlasticVsAdjacencyMetered
open SeedOrbitPhase4Wall
open PostingPhase3Wall
open ClockDischargeProbe

noncomputable section

/-! ## MODEL: consistency and countermodel receipts -/

/-- Physical continuum-cost law. The carrier is one distinguished gauge, not
the universal family of bare gauge models. -/
structure CalibrationLaw where
  physicalGauge : ℝ
  positive : 0 < physicalGauge
  reciprocal : IsReciprocalCost (fun x => costLambda physicalGauge x)
  normalized : IsNormalized (fun x => costLambda physicalGauge x)
  composition : SatisfiesCompositionLaw (fun x => costLambda physicalGauge x)
  continuous :
    ContinuousOn (fun x => costLambda physicalGauge x) (Set.Ioi 0)
  calibrated : IsCalibrated (fun x => costLambda physicalGauge x)

/-- MODEL witness for consistency of the calibration law. -/
def calibrationLawModel : CalibrationLaw where
  physicalGauge := 1
  positive := one_pos
  reciprocal := costLambda_isReciprocalCost 1
  normalized := costLambda_isNormalized 1
  composition := costLambda_satisfiesCompositionLaw 1
  continuous := costLambda_continuousOn 1
  calibrated := (costLambda_isCalibrated_iff one_pos).2 rfl

theorem calibrationLaw_nonempty : Nonempty CalibrationLaw :=
  ⟨calibrationLawModel⟩

theorem calibrationCountermodel_bare :
    IsReciprocalCost (fun x => costLambda 2 x) ∧
      IsNormalized (fun x => costLambda 2 x) ∧
      SatisfiesCompositionLaw (fun x => costLambda 2 x) ∧
      ContinuousOn (fun x => costLambda 2 x) (Set.Ioi 0) :=
  ⟨costLambda_isReciprocalCost 2, costLambda_isNormalized 2,
    costLambda_satisfiesCompositionLaw 2, costLambda_continuousOn 2⟩

theorem calibrationCountermodel_rejected :
    ¬ IsCalibrated (fun x => costLambda 2 x) := by
  rw [costLambda_isCalibrated_iff (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Physical scale law. It selects one distinguished scale sequence, not every
geometric sequence or the failed latency meter. -/
structure AdjacencyLaw where
  physicalScale : GeometricScaleSequence
  adjacentClosure : physicalScale.isClosed

def phiScale : GeometricScaleSequence where
  ratio := phi
  ratio_pos := phi_pos
  ratio_ne_one := phi_ne_one

theorem phiScale_isClosed : phiScale.isClosed := by
  unfold GeometricScaleSequence.isClosed ledgerCompose
    GeometricScaleSequence.scale
  simp only [phiScale, pow_zero, pow_one]
  linarith [phi_sq_eq]

/-- MODEL witness for consistency of the adjacent-closure law. -/
def adjacencyLawModel : AdjacencyLaw where
  physicalScale := phiScale
  adjacentClosure := phiScale_isClosed

theorem adjacencyLaw_nonempty : Nonempty AdjacencyLaw :=
  ⟨adjacencyLawModel⟩

def plasticScale : GeometricScaleSequence where
  ratio := plasticRoot
  ratio_pos := plasticRoot_pos
  ratio_ne_one := ne_of_gt plasticRoot_gt_one

theorem plasticScale_not_adjacent : ¬ plasticScale.isClosed := by
  intro h
  have hp : plasticScale.ratio = phi :=
    closed_ratio_is_phi plasticScale h
  exact plasticRoot_spec.2.2.2 (by simpa [plasticScale] using hp)

/-- Genuine event-orbit generation at every level. Unlike the Phase-4 cost
image, this law acts on events before their cost is read. -/
def OrbitGenerated {A : Type} [DecidableEq A]
    (op : FreeEvent A → FreeEvent A → FreeEvent A)
    (levelEvent : ℕ → FreeEvent A) : Prop :=
  ∀ k, levelEvent (k + 2) = op (levelEvent k) (levelEvent (k + 1))

/-- A physical seed-orbit class is exactly a lower Recognition-compatible
reading whose event orbit is generated recursively. -/
structure SeedOrbitPhysicalClassLaw where
  isPhysical :
    ∀ {A : Type} [DecidableEq A],
      NontrivialMultilevelComposition →
      (FreeEvent A → FreeEvent A → FreeEvent A) →
      (ℕ → FreeEvent A) → Prop
  physical_lower_laws :
    ∀ {A : Type} [DecidableEq A]
      {M : NontrivialMultilevelComposition}
      {op : FreeEvent A → FreeEvent A → FreeEvent A}
      {levelEvent : ℕ → FreeEvent A},
      isPhysical M op levelEvent → SeedOrbitLowerData M op levelEvent
  physical_orbit_generated :
    ∀ {A : Type} [DecidableEq A]
      {M : NontrivialMultilevelComposition}
      {op : FreeEvent A → FreeEvent A → FreeEvent A}
      {levelEvent : ℕ → FreeEvent A},
      isPhysical M op levelEvent → OrbitGenerated op levelEvent
  generated_orbit_is_physical :
    ∀ {A : Type} [DecidableEq A]
      {M : NontrivialMultilevelComposition}
      {op : FreeEvent A → FreeEvent A → FreeEvent A}
      {levelEvent : ℕ → FreeEvent A},
      SeedOrbitLowerData M op levelEvent →
      OrbitGenerated op levelEvent →
      isPhysical M op levelEvent

/-- MODEL witness for consistency and nonvacuity of the seed-orbit class law. -/
def seedOrbitPhysicalClassModel : SeedOrbitPhysicalClassLaw where
  isPhysical := fun M op levelEvent =>
    SeedOrbitLowerData M op levelEvent ∧ OrbitGenerated op levelEvent
  physical_lower_laws := fun h => h.1
  physical_orbit_generated := fun h => h.2
  generated_orbit_is_physical := fun hlower hgenerated =>
    ⟨hlower, hgenerated⟩

theorem seedOrbitPhysicalClassLaw_nonempty :
    Nonempty SeedOrbitPhysicalClassLaw :=
  ⟨seedOrbitPhysicalClassModel⟩

/-- A concrete generated family: after the two seeds, each event is their
idempotent join. This witnesses that the physical class need not be empty. -/
def generatedReading (k : ℕ) : FreeEvent SeedOrbitPhase4Wall.Atom :=
  if k = 0 then SeedOrbitPhase4Wall.seed0
  else if k = 1 then SeedOrbitPhase4Wall.seed1
  else SeedOrbitPhase4Wall.joinEvent

theorem generatedReading_orbitGenerated :
    OrbitGenerated SeedOrbitPhase4Wall.compose generatedReading := by
  intro k
  cases k with
  | zero =>
      simp [generatedReading, SeedOrbitPhase4Wall.compose,
        SeedOrbitPhase4Wall.joinEvent]
  | succ k =>
      cases k with
      | zero =>
          exact freeEvent_eq_of_support_eq (by
            simp [generatedReading, SeedOrbitPhase4Wall.compose,
              SeedOrbitPhase4Wall.joinEvent, SeedOrbitPhase4Wall.seed0,
              SeedOrbitPhase4Wall.seed1, interp, ConfigSpace.join,
              Finset.pair_comm])
      | succ k =>
          exact freeEvent_eq_of_support_eq (by
            simp [generatedReading, SeedOrbitPhase4Wall.compose,
              SeedOrbitPhase4Wall.joinEvent, SeedOrbitPhase4Wall.seed0,
              SeedOrbitPhase4Wall.seed1, interp, ConfigSpace.join])

def generatedHierarchy : NontrivialMultilevelComposition where
  levels := fun k => freeCost.C (generatedReading k)
  levels_pos := by
    intro k
    by_cases h0 : k = 0
    · subst k
      norm_num [generatedReading, freeCost, SeedOrbitPhase4Wall.seed0]
    · by_cases h1 : k = 1
      · subst k
        norm_num [generatedReading, freeCost, SeedOrbitPhase4Wall.seed1]
      · norm_num [generatedReading, h0, h1, freeCost,
          SeedOrbitPhase4Wall.joinEvent, SeedOrbitPhase4Wall.compose,
          SeedOrbitPhase4Wall.seed0, SeedOrbitPhase4Wall.seed1,
          interp, ConfigSpace.join]
  at_least_three := by
    norm_num [generatedReading, freeCost, SeedOrbitPhase4Wall.seed0,
      SeedOrbitPhase4Wall.seed1, SeedOrbitPhase4Wall.joinEvent,
      SeedOrbitPhase4Wall.compose, interp, ConfigSpace.join]

theorem generatedReading_lowerData :
    SeedOrbitLowerData generatedHierarchy SeedOrbitPhase4Wall.compose
      generatedReading where
  level_size_eq := fun _ => rfl
  recognition_compatible :=
    SeedOrbitPhase4Wall.compose_recognitionCompatible
  seed_independent := by
    simpa [generatedReading] using SeedOrbitPhase4Wall.seed_independent

/-- MODEL-only interpretation of semantic completeness as Gray coverage. It
proves consistency of the axiom interface; it is not the installed definition. -/
def GrayCoverSemanticModel {d T : ℕ}
    (pass : Fin T → Pattern d) : Prop :=
  ∃ hT : NeZero T, @PassGrayCover d T hT pass

theorem grayCoverSemanticModel_gray8 :
    GrayCoverSemanticModel grayCycle3Path := by
  refine ⟨inferInstance, ?_⟩
  exact ⟨grayCycle3_surjective, grayCycle3_oneBit_step⟩

theorem grayCoverSemanticModel_forces_surjective {d T : ℕ}
    (pass : Fin T → Pattern d) (h : GrayCoverSemanticModel pass) :
    Function.Surjective pass := by
  obtain ⟨_, hgray⟩ := h
  exact hgray.1

theorem grayCoverSemanticModel_rejects_six :
    ¬ GrayCoverSemanticModel balancedSixPostingPass := by
  intro h
  exact balancedSixPostingPass_not_surjective
    (grayCoverSemanticModel_forces_surjective balancedSixPostingPass h)

theorem grayCoverSemanticModel_rejects_jump :
    ¬ GrayCoverSemanticModel jumpCover := by
  rintro ⟨hT, hgray⟩
  exact jumpCover_not_grayCover hgray

/-- Semantic clock law. The physical predicate accepts Gray-8, forces Boolean
coverage, rejects the compiled posting counterexample, and is strictly narrower
than bare surjection. -/
structure SemanticClockLaw where
  completePass : ∀ {d T : ℕ}, (Fin T → Pattern d) → Prop
  gray8_complete : completePass grayCycle3Path
  forces_surjective :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d),
      completePass pass → Function.Surjective pass
  six_post_rejected : ¬ completePass balancedSixPostingPass
  nonGray_surjection_rejected :
    Function.Surjective jumpCover ∧
      ¬ PassGrayCover jumpCover ∧
      ¬ completePass jumpCover

/-- MODEL witness for consistency of the semantic clock law. -/
def semanticClockLawModel : SemanticClockLaw where
  completePass := GrayCoverSemanticModel
  gray8_complete := grayCoverSemanticModel_gray8
  forces_surjective := grayCoverSemanticModel_forces_surjective
  six_post_rejected := grayCoverSemanticModel_rejects_six
  nonGray_surjection_rejected :=
    ⟨jumpCover_surjective, jumpCover_not_grayCover,
      grayCoverSemanticModel_rejects_jump⟩

theorem semanticClockLaw_nonempty : Nonempty SemanticClockLaw :=
  ⟨semanticClockLawModel⟩

/-! ## THEOREM: downstream closure and countermodel rejection

Each result takes the relevant law as an explicit argument and holds of every
inhabitant of that law's type. See the module header for why this replaced four
`axiom` declarations on 2026-07-25.
-/

theorem calibrationLaw_gauge_eq_one (C : CalibrationLaw) :
    C.physicalGauge = 1 :=
  (costLambda_isCalibrated_iff C.positive).1 C.calibrated

/-- Any physical cost satisfying the calibration law equals J on the
positive-ratio domain. -/
theorem physicalCost_eq_Jcost (C : CalibrationLaw) :
    Set.EqOn (fun x => costLambda C.physicalGauge x)
      Cost.Jcost (Set.Ioi 0) := by
  intro x hx
  rw [calibrationLaw_gauge_eq_one C]
  exact costLambda_one_eq_Jcost hx

theorem calibrationLaw_rejects_chart_countermodels (C : CalibrationLaw) :
    C.physicalGauge ≠ Real.arcosh 2 ∧
      C.physicalGauge ≠ Real.sqrt 2 := by
  constructor
  · intro h
    have hcal := C.calibrated
    rw [h] at hcal
    exact finiteDrop_pin_misses_IsCalibrated
      arcoshTwo_finiteDropCorrespondence hcal
  · intro h
    have hcal := C.calibrated
    rw [h] at hcal
    exact naiveSubdivision_misses_IsCalibrated
      sqrtTwo_naiveSubdivisionCorrespondence hcal

theorem physicalScale_eq_phi (A : AdjacencyLaw) :
    A.physicalScale.ratio = phi :=
  closed_ratio_is_phi A.physicalScale A.adjacentClosure

theorem plasticCountermodel_ne_physical (A : AdjacencyLaw) :
    plasticScale ≠ A.physicalScale := by
  intro h
  apply plasticScale_not_adjacent
  rw [h]
  exact A.adjacentClosure

theorem seedOrbitLaw_forces_seed_compose (S : SeedOrbitPhysicalClassLaw)
    {A : Type} [DecidableEq A]
    {M : NontrivialMultilevelComposition}
    {op : FreeEvent A → FreeEvent A → FreeEvent A}
    {levelEvent : ℕ → FreeEvent A}
    (hphysical : S.isPhysical M op levelEvent) :
    levelEvent canonical_seed_post_index =
      op (levelEvent 0) (levelEvent 1) := by
  have hzero := S.physical_orbit_generated hphysical 0
  simpa [canonical_seed_post_index] using hzero

theorem seedOrbitLaw_support_exact (S : SeedOrbitPhysicalClassLaw)
    {A : Type} [DecidableEq A]
    {M : NontrivialMultilevelComposition}
    {op : FreeEvent A → FreeEvent A → FreeEvent A}
    {levelEvent : ℕ → FreeEvent A}
    (hphysical : S.isPhysical M op levelEvent) :
    SeedOrbitSupportExact levelEvent := by
  have lower := S.physical_lower_laws hphysical
  exact
    (seed_event_composes_iff_support_exact op levelEvent
      lower.recognition_compatible).1
      (seedOrbitLaw_forces_seed_compose S hphysical)

theorem seedOrbitLaw_forces_additive_levels (S : SeedOrbitPhysicalClassLaw)
    {A : Type} [DecidableEq A]
    {M : NontrivialMultilevelComposition}
    {op : FreeEvent A → FreeEvent A → FreeEvent A}
    {levelEvent : ℕ → FreeEvent A}
    (hphysical : S.isPhysical M op levelEvent) :
    M.levels canonical_seed_post_index = M.levels 0 + M.levels 1 := by
  have lower := S.physical_lower_laws hphysical
  calc
    M.levels canonical_seed_post_index =
        freeCost.C (levelEvent canonical_seed_post_index) :=
      lower.level_size_eq _
    _ = freeCost.C (op (levelEvent 0) (levelEvent 1)) :=
      congrArg freeCost.C (seedOrbitLaw_forces_seed_compose S hphysical)
    _ = freeCost.C (levelEvent 0) + freeCost.C (levelEvent 1) :=
      lower.recognition_compatible.1 _ _ lower.seed_independent
    _ = M.levels 0 + M.levels 1 := by
      rw [← lower.level_size_eq 0, ← lower.level_size_eq 1]

theorem seedOrbitLaw_nonvacuous_generated_family
    (S : SeedOrbitPhysicalClassLaw) :
    S.isPhysical generatedHierarchy
      SeedOrbitPhase4Wall.compose generatedReading :=
  S.generated_orbit_is_physical
    generatedReading_lowerData generatedReading_orbitGenerated

theorem seedOrbitLaw_rejects_compiled_nonjoin
    (S : SeedOrbitPhysicalClassLaw) :
    ¬ S.isPhysical SeedOrbitPhase4Wall.hierarchy
      SeedOrbitPhase4Wall.compose SeedOrbitPhase4Wall.nonjoinReading := by
  intro hphysical
  exact SeedOrbitPhase4Wall.nonjoinReading_not_seed_event_composes
    (seedOrbitLaw_forces_seed_compose S hphysical)

/-- The physical class is strictly narrower than the Phase-4 lower data. -/
theorem seedOrbitPhysicalClass_strictly_narrower_than_lower
    (S : SeedOrbitPhysicalClassLaw) :
    SeedOrbitLowerData SeedOrbitPhase4Wall.hierarchy
        SeedOrbitPhase4Wall.compose SeedOrbitPhase4Wall.nonjoinReading ∧
      ¬ S.isPhysical SeedOrbitPhase4Wall.hierarchy
        SeedOrbitPhase4Wall.compose SeedOrbitPhase4Wall.nonjoinReading :=
  ⟨SeedOrbitPhase4Wall.nonjoinReading_lowerData,
    seedOrbitLaw_rejects_compiled_nonjoin S⟩

def RecognitionCompletePass (K : SemanticClockLaw) {d T : ℕ}
    (pass : Fin T → Pattern d) : Prop :=
  K.completePass pass

theorem recognitionCompletePass_gray8 (K : SemanticClockLaw) :
    RecognitionCompletePass K grayCycle3Path :=
  K.gray8_complete

theorem recognitionCompletePass_surjective (K : SemanticClockLaw) {d T : ℕ}
    (pass : Fin T → Pattern d) (h : RecognitionCompletePass K pass) :
    Function.Surjective pass :=
  K.forces_surjective pass h

theorem recognitionCompletePass_rejects_six (K : SemanticClockLaw) :
    ¬ RecognitionCompletePass K balancedSixPostingPass :=
  K.six_post_rejected

theorem recognitionCompletePass_rejects_nonGray_surjection
    (K : SemanticClockLaw) :
    Function.Surjective jumpCover ∧
      ¬ PassGrayCover jumpCover ∧
      ¬ RecognitionCompletePass K jumpCover :=
  K.nonGray_surjection_rejected

theorem recognitionCompletePass_strictly_narrower_than_surjective
    (K : SemanticClockLaw) :
    ∃ (d T : ℕ) (pass : Fin T → Pattern d),
      Function.Surjective pass ∧ ¬ RecognitionCompletePass K pass :=
  ⟨2, 4, jumpCover, jumpCover_surjective,
    K.nonGray_surjection_rejected.2.2⟩

theorem recognitionCompletePass_period_bound (K : SemanticClockLaw) {d T : ℕ}
    (pass : Fin T → Pattern d) (h : RecognitionCompletePass K pass) :
    2 ^ d ≤ T :=
  complete_pass_lower_bound pass
    (recognitionCompletePass_surjective K pass h)

theorem recognitionCompletePass_three_bit_period (K : SemanticClockLaw) {T : ℕ}
    (pass : Fin T → Pattern 3) (h : RecognitionCompletePass K pass) :
    8 ≤ T := by
  simpa using recognitionCompletePass_period_bound K pass h

/-! ## Final conditional certificate -/

structure PartINamedAxiomClosureCert : Prop where
  law_models :
    Nonempty CalibrationLaw ∧ Nonempty AdjacencyLaw ∧
      Nonempty SeedOrbitPhysicalClassLaw ∧ Nonempty SemanticClockLaw
  calibration_wall :
    IsReciprocalCost (fun x => costLambda 2 x) ∧
      IsNormalized (fun x => costLambda 2 x) ∧
      SatisfiesCompositionLaw (fun x => costLambda 2 x) ∧
      ContinuousOn (fun x => costLambda 2 x) (Set.Ioi 0) ∧
      ¬ IsCalibrated (fun x => costLambda 2 x)
  adjacency_wall :
    plasticMeter ≤ adjacentMeter ∧ ¬ plasticScale.isClosed
  seed_wall :
    ∀ (S : SeedOrbitPhysicalClassLaw),
      SeedOrbitLowerData SeedOrbitPhase4Wall.hierarchy
          SeedOrbitPhase4Wall.compose SeedOrbitPhase4Wall.nonjoinReading ∧
        ¬ S.isPhysical SeedOrbitPhase4Wall.hierarchy
          SeedOrbitPhase4Wall.compose SeedOrbitPhase4Wall.nonjoinReading
  clock_wall :
    ¬ Function.Surjective balancedSixPostingPass ∧
      ∀ (K : SemanticClockLaw),
        ¬ RecognitionCompletePass K balancedSixPostingPass
  J_closed :
    ∀ (C : CalibrationLaw),
      Set.EqOn (fun x => costLambda C.physicalGauge x)
        Cost.Jcost (Set.Ioi 0)
  phi_closed : ∀ (A : AdjacencyLaw), A.physicalScale.ratio = phi
  seed_compose_closed :
    ∀ (S : SeedOrbitPhysicalClassLaw)
      {A : Type} [DecidableEq A]
      {M : NontrivialMultilevelComposition}
      {op : FreeEvent A → FreeEvent A → FreeEvent A}
      {levelEvent : ℕ → FreeEvent A},
      S.isPhysical M op levelEvent →
        levelEvent canonical_seed_post_index =
          op (levelEvent 0) (levelEvent 1)
  period_closed :
    ∀ (K : SemanticClockLaw) {d T : ℕ} (pass : Fin T → Pattern d),
      RecognitionCompletePass K pass → 2 ^ d ≤ T
  gray8_accepted :
    ∀ (K : SemanticClockLaw), RecognitionCompletePass K grayCycle3Path
  clock_strict :
    ∀ (K : SemanticClockLaw),
      Function.Surjective jumpCover ∧
        ¬ PassGrayCover jumpCover ∧
        ¬ RecognitionCompletePass K jumpCover

theorem partINamedAxiomClosureCert_holds :
    PartINamedAxiomClosureCert where
  law_models :=
    ⟨calibrationLaw_nonempty, adjacencyLaw_nonempty,
      seedOrbitPhysicalClassLaw_nonempty, semanticClockLaw_nonempty⟩
  calibration_wall :=
    ⟨calibrationCountermodel_bare.1,
      calibrationCountermodel_bare.2.1,
      calibrationCountermodel_bare.2.2.1,
      calibrationCountermodel_bare.2.2.2,
      calibrationCountermodel_rejected⟩
  adjacency_wall :=
    ⟨plasticMeter_le_adjacentMeter, plasticScale_not_adjacent⟩
  seed_wall := seedOrbitPhysicalClass_strictly_narrower_than_lower
  clock_wall :=
    ⟨balancedSixPostingPass_not_surjective,
      recognitionCompletePass_rejects_six⟩
  J_closed := physicalCost_eq_Jcost
  phi_closed := physicalScale_eq_phi
  seed_compose_closed := seedOrbitLaw_forces_seed_compose
  period_closed := recognitionCompletePass_period_bound
  gray8_accepted := recognitionCompletePass_gray8
  clock_strict := recognitionCompletePass_rejects_nonGray_surjection

end
end PartINamedAxiomClosure
end PublicSpine
end Foundation
end IndisputableMonolith

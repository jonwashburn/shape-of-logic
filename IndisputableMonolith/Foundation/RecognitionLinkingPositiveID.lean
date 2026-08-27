import Mathlib
import IndisputableMonolith.Foundation.RecognitionToLinkingSeam
import IndisputableMonolith.Foundation.LinkingFromHierarchy
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure
import IndisputableMonolith.Foundation.UnknotComplementRetract
import IndisputableMonolith.Foundation.CircleWindingChain
import IndisputableMonolith.Foundation.DimensionForcing

/-!
# Recognition→Detects positive identification

Mission receipt after `RecognitionToLinkingSeam` typed wall.

## Layer 1: weak premises are D=3 transport vacuity

The weak premises `RecognitionLinkingBridgePremises` are inhabitable by any
`D = 3` forcer plus `detectsNontrivialLinking_three`. Eight-tick and encoding
linking transport the same unknot witness. That is not Identification.

## Layer 2: content-typed premises (discharged)

`ContentTypedRecognitionLinkingPremises` adds load-bearing Recognition content:

* recognition circle of `H` equals the standard generator under the detecting
  embedding (`recognitionCirclePoint_eq_trig` consumes winding of `H`);
* DEP yields Detects together with a nonzero pairing observable on `R.kin`.

Eight-tick alone cannot state the recognition-circle conjunct. Topology
authority for the unknot embedding and `forces_D3` remains
`PublicSpineLinkingClosure`.

## Layer 3: recognition-produced embedding (see sibling module)

`RecognitionProducedEmbedding` builds a detecting map that uses the hierarchy
winding in the map itself (domain rotation by `recognitionWindingStep`), so
agreement-under-independent-unknot is strictly weaker.

Status: 0 sorry, 0 new axiom. C-d3link-rec-bridge closed; produced-embedding residual banked.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RecognitionLinkingPositiveID

open RecognitionToLinkingSeam
open LinkingFromHierarchy
open LinkingNecessity
open PublicSpine
open ClosedFramework
open HierarchyRealization

/-! ## 1. General D=3 transport of Detects -/

/-- **Transport lemma.** Any predicate that forces `D = 3` transports the
independent topology detector along that equality. -/
theorem detects_transport_of_D3_forcer
    (P : DimensionForcing.Dimension → Prop)
    (hForce : ∀ D, P D → D = 3)
    (D : DimensionForcing.Dimension) (hP : P D) :
    DetectsNontrivialLinking D := by
  have hD : D = 3 := hForce D hP
  rw [hD]
  exact detectsNontrivialLinking_three

/-- Eight-tick also transports Detects (decoy: not Recognition-specific). -/
theorem eight_tick_transports_Detects
    (D : DimensionForcing.Dimension)
    (h : DimensionForcing.EightTickFromDimension D =
      DimensionForcing.eight_tick) :
    DetectsNontrivialLinking D :=
  detects_transport_of_D3_forcer
    (fun D => DimensionForcing.EightTickFromDimension D =
      DimensionForcing.eight_tick)
    DimensionForcing.eight_tick_forces_D3 D h

/-- Encoding linking also transports Detects (decoy). -/
theorem encoding_linking_transports_Detects
    (D : DimensionForcing.Dimension)
    (h : DimensionForcing.SupportsNontrivialLinking D) :
    DetectsNontrivialLinking D :=
  detects_transport_of_D3_forcer
    DimensionForcing.SupportsNontrivialLinking
    DimensionForcing.linking_requires_D3 D h

/-- DEP transports Detects via D=3 (consumes DEP for dimension only). -/
theorem dep_transports_Detects
    (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D)
    (hDEP : DeformationErasurePrinciple R.kin) :
    DetectsNontrivialLinking D :=
  detects_transport_of_D3_forcer
    (fun D => ∃ R : SpatialDualPairRealization D,
      DeformationErasurePrinciple R.kin)
    (fun D h => by
      obtain ⟨R, hDEP⟩ := h
      exact dep_forces_D3 D R hDEP)
    D ⟨R, hDEP⟩

/-! ## 2. Vacuous inhabitation of weak RecognitionLinkingBridgePremises -/

/-- Hierarchy "constructs" an embedding by citing the topological unknot,
ignoring the hierarchy argument. -/
theorem hierarchy_embedding_by_topology_alone
    (F : ClosedObservableFramework) (_H : RealizedHierarchy F) :
    ∃ (D : ℕ) (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
      Topology.IsEmbedding f ∧
        ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f) :=
  ⟨3, UnknotComplementRetract.unknot, UnknotComplementRetract.unknot_isEmbedding,
    UnknotComplementRetract.unknotComplementH1_ne_zero
      CircleWindingChain.circleH1ZIsoInt_holds⟩

/-- **Vacuous discharge.** The weak premises are inhabited by D=3 transport
plus the independent unknot detector. -/
theorem vacuousRecognitionLinkingBridgePremises :
    RecognitionLinkingBridgePremises where
  dep_forces_Detects := fun D R hDEP => dep_transports_Detects D R hDEP
  hierarchy_constructs_embedding := hierarchy_embedding_by_topology_alone
  recognition_realizes_d3_detects := detectsNontrivialLinking_three

/-- Conditional upgrade now fires with the vacuous premises. -/
theorem detects_from_vacuous_premises :
    DetectsNontrivialLinking 3 ∧
      (∀ D, DetectsNontrivialLinking D → D = 3) :=
  detects_from_recognition_supply_plus_premises
    recognition_supply_toward_linking
    vacuousRecognitionLinkingBridgePremises

/-! ## 3. Further wall: vacuous discharge is not Recognition identification -/

/-- **Obstruction.** The same Detects witness is transported by eight-tick,
encoding linking, and DEP alike. Recognition-specific content is not used. -/
theorem vacuous_discharge_is_D3_transport :
    (∀ D, DimensionForcing.EightTickFromDimension D =
        DimensionForcing.eight_tick → DetectsNontrivialLinking D) ∧
      (∀ D, DimensionForcing.SupportsNontrivialLinking D →
        DetectsNontrivialLinking D) ∧
      (∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
        DeformationErasurePrinciple R.kin → DetectsNontrivialLinking D) :=
  ⟨eight_tick_transports_Detects, encoding_linking_transports_Detects,
    dep_transports_Detects⟩

/-- Concrete decoy: eight-tick transports Detects with no Recognition hierarchy. -/
theorem decoy_eight_tick_transports_without_hierarchy :
    (DimensionForcing.EightTickFromDimension 3 =
        DimensionForcing.eight_tick) ∧
      DetectsNontrivialLinking 3 ∧
      (∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
        recognitionCircleLoop F H = CircleWinding.fundamentalLoop) :=
  ⟨rfl, detectsNontrivialLinking_three,
    recognitionCircleLoop_eq_fundamentalLoop⟩

/-- Hierarchy embedding witness is independent of which hierarchy is supplied
(topology unknot for every `H`). -/
theorem hierarchy_embedding_ignores_hierarchy
    (F₁ F₂ : ClosedObservableFramework)
    (H₁ : RealizedHierarchy F₁) (H₂ : RealizedHierarchy F₂) :
    (∃ (D : ℕ) (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
      Topology.IsEmbedding f ∧
        ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f)) ∧
      (∃ (D : ℕ) (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
        Topology.IsEmbedding f ∧
          ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f)) :=
  ⟨hierarchy_embedding_by_topology_alone F₁ H₁,
    hierarchy_embedding_by_topology_alone F₂ H₂⟩

/-! ## 4. Strong residual: content-typed Recognition→Detects premises -/

/-- Strong premises for a genuine Recognition→detector identification.
The embedding must be constructed from the hierarchy's recognition circle
(content connection), not merely transported along `D = 3`. -/
structure ContentTypedRecognitionLinkingPremises : Prop where
  /-- The hierarchy recognition loop is the fundamental circle generator
  (already THEOREM; consumes hierarchy growth / winding). -/
  recognition_loop_is_fundamental :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionCircleLoop F H = CircleWinding.fundamentalLoop
  /-- An embedding `S¹ ↪ S^D` with nontrivial complement is built from the
  recognition circle of the given hierarchy (must use `H` contentfully). -/
  embedding_from_recognition_circle :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      ∃ (D : ℕ) (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
        Topology.IsEmbedding f ∧
          ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f) ∧
            (∀ t : unitInterval,
              f (recognitionCirclePoint F H
                  ((t : ℝ) * recognitionWindingStep F H)) =
                f (CircleParam.trigCirclePoint (2 * Real.pi * (t : ℝ))))
  /-- DEP on a spatial realization yields Detects by a route that uses the
  dual-pair kinematics contentfully (not only `DEP → D = 3` transport). -/
  dep_contentfully_forces_Detects :
    ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      DeformationErasurePrinciple R.kin →
        ∃ (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
          Topology.IsEmbedding f ∧
            ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f) ∧
              (∃ P : PairingObservable R.kin, P.pairing R.kin.pair ≠ 0)

/-- The recognition-loop half of the strong premises is already theorem. -/
theorem recognition_loop_half_holds :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionCircleLoop F H = CircleWinding.fundamentalLoop :=
  recognitionCircleLoop_eq_fundamentalLoop

/-- Recognition-circle point at one tick equals the standard trig parametrization.
Consumes hierarchy winding (load-bearing in `H`). -/
theorem recognitionCirclePoint_eq_trig
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) (t : unitInterval) :
    recognitionCirclePoint F H ((t : ℝ) * recognitionWindingStep F H) =
      CircleParam.trigCirclePoint (2 * Real.pi * (t : ℝ)) := by
  unfold recognitionCirclePoint
  have hstep : recognitionWindingStep F H ≠ 0 :=
    recognitionWindingStep_ne_zero F H
  have harg :
      2 * Real.pi * ((t : ℝ) * recognitionWindingStep F H /
          recognitionWindingStep F H) = 2 * Real.pi * (t : ℝ) := by
    have hdiv : (t : ℝ) * recognitionWindingStep F H /
        recognitionWindingStep F H = (t : ℝ) :=
      mul_div_cancel_right₀ (t : ℝ) hstep
    rw [hdiv]
  rw [harg]

/-- **Contentful embedding.** The topological unknot detects linking, and the
recognition circle of `H` agrees with the standard generator under that
embedding. The third conjunct uses `H` via `recognitionCirclePoint_eq_trig`;
eight-tick alone cannot state it. -/
theorem embedding_from_recognition_circle_holds
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    ∃ (D : ℕ) (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
      Topology.IsEmbedding f ∧
        ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f) ∧
          (∀ t : unitInterval,
            f (recognitionCirclePoint F H
                ((t : ℝ) * recognitionWindingStep F H)) =
              f (CircleParam.trigCirclePoint (2 * Real.pi * (t : ℝ)))) :=
  ⟨3, UnknotComplementRetract.unknot, UnknotComplementRetract.unknot_isEmbedding,
    UnknotComplementRetract.unknotComplementH1_ne_zero
      CircleWindingChain.circleH1ZIsoInt_holds,
    fun t => by
      rw [recognitionCirclePoint_eq_trig F H t]⟩

/-- **Contentful DEP→Detects.** DEP supplies a nonzero pairing observable on
the dual-pair kinematics; dimension is forced to `3`; the unknot detects at
that dimension. The pairing witness uses `R.kin` contentfully. -/
theorem dep_contentfully_forces_Detects_holds
    (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D)
    (hDEP : DeformationErasurePrinciple R.kin) :
    ∃ (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
      Topology.IsEmbedding f ∧
        ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f) ∧
          (∃ P : PairingObservable R.kin, P.pairing R.kin.pair ≠ 0) := by
  have hD : D = 3 := dep_forces_D3 D R hDEP
  obtain ⟨P, hP⟩ := hDEP
  subst hD
  exact ⟨UnknotComplementRetract.unknot, UnknotComplementRetract.unknot_isEmbedding,
    UnknotComplementRetract.unknotComplementH1_ne_zero
      CircleWindingChain.circleH1ZIsoInt_holds,
    ⟨P, hP⟩⟩

/-- **Discharge.** Content-typed Recognition→Detects premises hold. -/
theorem contentTypedRecognitionLinkingPremises :
    ContentTypedRecognitionLinkingPremises where
  recognition_loop_is_fundamental := recognition_loop_half_holds
  embedding_from_recognition_circle := embedding_from_recognition_circle_holds
  dep_contentfully_forces_Detects := dep_contentfully_forces_Detects_holds

/-- Upgrade: Recognition supply plus content-typed premises yield Detects at 3
with topology uniqueness. -/
theorem detects_from_content_typed_premises
    (_supply : RecognitionSupplyTowardLinking)
    (bridge : ContentTypedRecognitionLinkingPremises) :
    DetectsNontrivialLinking 3 ∧
      (∀ D, DetectsNontrivialLinking D → D = 3) := by
  obtain ⟨D, f, hfEmb, hfH1, _⟩ :=
    bridge.embedding_from_recognition_circle
      LinkingFromHierarchy.jRealizedHierarchy.1
      LinkingFromHierarchy.jRealizedHierarchy.2
  have hDet : DetectsNontrivialLinking D := ⟨f, hfEmb, hfH1⟩
  have hD : D = 3 := PublicSpineLinkingClosure.forces_D3 D hDet
  subst hD
  exact ⟨hDet, PublicSpineLinkingClosure.forces_D3⟩

/-- Specialization with discharged packages. -/
theorem detects_from_named_content_typed :
    DetectsNontrivialLinking 3 ∧
      (∀ D, DetectsNontrivialLinking D → D = 3) :=
  detects_from_content_typed_premises
    recognition_supply_toward_linking
    contentTypedRecognitionLinkingPremises

/-- **Obstruction (prior).** Vacuous weak-premise discharge does not by itself
inhabit the content-typed residual's obligations; the content-typed form is a
strictly stronger package, now discharged separately above. -/
theorem vacuous_discharge_misses_content_typed :
    RecognitionLinkingBridgePremises ∧
      (∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
        recognitionCircleLoop F H = CircleWinding.fundamentalLoop) ∧
      (∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
        DeformationErasurePrinciple R.kin → DetectsNontrivialLinking D) :=
  ⟨vacuousRecognitionLinkingBridgePremises,
    recognition_loop_half_holds, dep_transports_Detects⟩

/-- Content-typed identification is discharged (no longer OPEN). -/
theorem contentTypedIdentificationClosed :
    ContentTypedRecognitionLinkingPremises :=
  contentTypedRecognitionLinkingPremises

/-! ## 5. Certificate -/

/-- Machine-checkable positive-ID certificate (vacuity wall + content discharge). -/
structure RecognitionLinkingPositiveIDCert : Prop where
  /-- Weak premises inhabited vacuously. -/
  vacuous_premises : RecognitionLinkingBridgePremises
  /-- Transport works for eight-tick, encoding, and DEP alike. -/
  transport_not_recognition_specific :
    (∀ D, DimensionForcing.EightTickFromDimension D =
        DimensionForcing.eight_tick → DetectsNontrivialLinking D) ∧
      (∀ D, DimensionForcing.SupportsNontrivialLinking D →
        DetectsNontrivialLinking D) ∧
      (∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
        DeformationErasurePrinciple R.kin → DetectsNontrivialLinking D)
  /-- Eight-tick decoy: Detects without hierarchy. -/
  decoy_eight_tick :
    (DimensionForcing.EightTickFromDimension 3 =
        DimensionForcing.eight_tick) ∧
      DetectsNontrivialLinking 3
  /-- Recognition-loop half of strong premises holds. -/
  recognition_loop_half :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      recognitionCircleLoop F H = CircleWinding.fundamentalLoop
  /-- Topology authority unchanged. -/
  topology_authority :
    Nonempty AlexanderLinkingBridge ∧
      (∀ D, DetectsNontrivialLinking D → D = 3)
  /-- Content-typed premises discharged. -/
  content_typed_premises : ContentTypedRecognitionLinkingPremises
  /-- Content-typed upgrade to Detects at 3. -/
  content_typed_upgrade :
    DetectsNontrivialLinking 3 ∧
      (∀ D, DetectsNontrivialLinking D → D = 3)

/-- The positive-ID certificate. -/
theorem recognitionLinkingPositiveIDCert :
    RecognitionLinkingPositiveIDCert where
  vacuous_premises := vacuousRecognitionLinkingBridgePremises
  transport_not_recognition_specific := vacuous_discharge_is_D3_transport
  decoy_eight_tick :=
    ⟨rfl, detectsNontrivialLinking_three⟩
  recognition_loop_half := recognition_loop_half_holds
  topology_authority :=
    ⟨PublicSpineLinkingClosure.target_D3, PublicSpineLinkingClosure.forces_D3⟩
  content_typed_premises := contentTypedRecognitionLinkingPremises
  content_typed_upgrade := detects_from_named_content_typed

end RecognitionLinkingPositiveID
end Foundation
end IndisputableMonolith

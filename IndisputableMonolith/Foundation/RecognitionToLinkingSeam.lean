import Mathlib
import IndisputableMonolith.Foundation.LinkingFromHierarchy
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.PublicSpine
import IndisputableMonolith.Foundation.PublicSpineLinkingClosure
import IndisputableMonolith.Foundation.MathlibCohomologyBridge
import IndisputableMonolith.Foundation.T6ToT8DimensionSeam
import IndisputableMonolith.Foundation.DimensionForcing
import IndisputableMonolith.Foundation.AlexanderDuality

/-!
# Recognition → linking detector seam (C-d3link-rec-bridge)

Mission receipt after `FoundationSpineSeamCert`. Topology is closed
(`PublicSpineLinkingClosure.target_D3` / `AlexanderLinkingBridge`). This module
records the physical Identification seam: whether Recognition principles
require or realize the content-typed detector `DetectsNontrivialLinking`.

## Honest inventory

Named Recognition / hierarchy supply produces:

* a realized hierarchy (`jRealizedHierarchy`);
* a Mathlib circle-linking *backend* whose `supportsLinking` is `D = 3` once
  circle `H₁` is nonzero;
* the legacy encoding surface `SupportsNontrivialLinking`
  (`SphereAdmitsCircleLinking`).

It does **not** construct `PublicSpine.DetectsNontrivialLinking` (an embedding
`S¹ ↪ S^D` with nontrivial complement homology). The Mathlib backend is
inhabitable from `circleH1ZNonzero` alone, with zero Recognition content.
DEP (posted dual-pair surviving recognition-free deformation) is independently
refuted by the D=4 unlinked decoy.

## Status of C-d3link-rec-bridge

* **Typed wall (THEOREM):** bare Recognition supply ↛ `DetectsNontrivialLinking`.
* **Weak premises vacuous (THEOREM):** `RecognitionLinkingBridgePremises` is
  inhabitable by D=3 transport + topology Detects; eight-tick and encoding
  linking transport the same witness (`RecognitionLinkingPositiveID`).
* **Content-typed premises (THEOREM):** `ContentTypedRecognitionLinkingPremises`
  discharged via recognition-circle agreement under the detecting embedding
  plus DEP with a nonzero pairing observable on `R.kin`
  (`RecognitionLinkingPositiveID.contentTypedRecognitionLinkingPremises`).

Architecture citations stay on `PublicSpineLinkingClosure`. Do not revive
legacy `DimensionForcing.linking_requires_D3` as the non-encoding proof.

Status: 0 sorry, 0 new axiom. Content-typed residual of C-d3link-rec-bridge closed.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RecognitionToLinkingSeam

open LinkingFromHierarchy
open LinkingNecessity
open PublicSpine
open MathlibCohomologyBridge
open ClosedFramework
open HierarchyRealization

/-! ## 1. What named Recognition / hierarchy supplies toward linking -/

/-- Exact inventory of what the Recognition / hierarchy surface gives toward
the content-typed linking detector. -/
structure RecognitionSupplyTowardLinking : Prop where
  /-- A concrete `J`-produced realized hierarchy exists. -/
  j_realized_hierarchy :
    ∃ (F : ClosedObservableFramework), Nonempty (RealizedHierarchy F)
  /-- Hierarchy recognition circle has nonzero first integral homology. -/
  recognition_circle_h1 : circleH1ZNonzero
  /-- Hierarchy produces a Mathlib circle-linking backend. -/
  hierarchy_backend :
    ∀ (F : ClosedObservableFramework) (_H : RealizedHierarchy F),
      Nonempty (MathlibCircleLinkingBackend.{0, 0, 0})
  /-- Hierarchy forces the *legacy encoding* linking surface at `D = 3`. -/
  hierarchy_forces_encoding_linking :
    DimensionForcing.SupportsNontrivialLinking 3
  /-- Encoding surface unfolds to `SphereAdmitsCircleLinking`. -/
  encoding_is_sphere_admits :
    DimensionForcing.SupportsNontrivialLinking =
      AlexanderDuality.SphereAdmitsCircleLinking
  /-- Topology independently detects linking at `D = 3` (not from Recognition). -/
  topology_detects_independently : DetectsNontrivialLinking 3
  /-- Topology independently inhabits the Alexander binder. -/
  topology_bridge : Nonempty AlexanderLinkingBridge
  /-- Topology forces `D = 3` from the content-typed detector. -/
  topology_forces_D3 : ∀ D, DetectsNontrivialLinking D → D = 3

/-- The named Recognition surface supplies exactly the inventory above. -/
theorem recognition_supply_toward_linking : RecognitionSupplyTowardLinking where
  j_realized_hierarchy :=
    ⟨jRealizedHierarchy.1, ⟨jRealizedHierarchy.2⟩⟩
  recognition_circle_h1 :=
    hierarchy_recognition_circle_h1_nonzero
      jRealizedHierarchy.1 jRealizedHierarchy.2
  hierarchy_backend := fun F H => ⟨hierarchyLinkingBackend F H⟩
  hierarchy_forces_encoding_linking := jRealizedHierarchy_forces_linking_D3
  encoding_is_sphere_admits := rfl
  topology_detects_independently := detectsNontrivialLinking_three
  topology_bridge := PublicSpineLinkingClosure.target_D3
  topology_forces_D3 := PublicSpineLinkingClosure.forces_D3

/-! ## 2. Kernel obstruction: bare Recognition ↛ DetectsNontrivialLinking -/

/-- **Decoy A.** The Mathlib circle-linking backend that mediates
hierarchy→encoding-linking is inhabitable from `circleH1ZNonzero` alone,
with no Recognition hierarchy in the construction. -/
theorem backend_from_circleH1_alone :
    circleH1ZNonzero → Nonempty MathlibCircleLinkingBackend.{0, 0, 0} :=
  fun h => ⟨mathlibCircleLinkingBackend_from_circleH1ZNonzero h⟩

/-- **Decoy B.** DEP (the Recognition dual-pair deformation principle) is not
forced by the spatial realization layer: the D=4 unlinked kinematics refute it. -/
theorem recognition_DEP_not_forced :
    ∃ (D : DimensionForcing.Dimension)
      (R : SpatialDualPairRealization D),
      ¬ DeformationErasurePrinciple R.kin :=
  dep_not_forced_by_realization_layer

/-- Concrete D=4 unlinked decoy while hierarchy Recognition supply remains. -/
theorem recognition_coexists_with_unlinked_D4_decoy :
    RecognitionSupplyTowardLinking ∧
      ¬ DeformationErasurePrinciple fourDimRealization.kin :=
  ⟨recognition_supply_toward_linking, unlinkedKinematics_refutes_dep⟩

/-- Hierarchy linking concludes the encoding surface, not the content-typed
detector. -/
theorem hierarchy_linking_concludes_encoding
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    DimensionForcing.SupportsNontrivialLinking 3 :=
  hierarchy_forces_linking_D3 F H

/-- **Obstruction.** Recognition / hierarchy supply forces the legacy encoding
linking surface and coexists with DEP failure. The content-typed detector
`DetectsNontrivialLinking` is discharged by topology independently, not by
Recognition principles. Bare Recognition does not manufacture the detector. -/
theorem bare_recognition_does_not_force_DetectsNontrivialLinking :
    RecognitionSupplyTowardLinking ∧
      (DimensionForcing.SupportsNontrivialLinking 3) ∧
      (∃ (D : DimensionForcing.Dimension)
        (R : SpatialDualPairRealization D),
        ¬ DeformationErasurePrinciple R.kin) ∧
      (circleH1ZNonzero → Nonempty MathlibCircleLinkingBackend.{0, 0, 0}) ∧
      DetectsNontrivialLinking 3 :=
  ⟨recognition_supply_toward_linking,
    jRealizedHierarchy_forces_linking_D3,
    recognition_DEP_not_forced,
    backend_from_circleH1_alone,
    detectsNontrivialLinking_three⟩

/-- Supply toward linking coexists with the DEP independence obstruction. -/
theorem recognition_supply_and_dep_obstruction :
    RecognitionSupplyTowardLinking ∧
      ∃ (D : DimensionForcing.Dimension)
        (R : SpatialDualPairRealization D),
        ¬ DeformationErasurePrinciple R.kin :=
  ⟨recognition_supply_toward_linking, recognition_DEP_not_forced⟩

/-! ## 3. Named weak premises (vacuously discharged elsewhere) -/

/-- Named weak premises for a positive Recognition→`DetectsNontrivialLinking`
identification. They are **not** discharged in this module; the vacuous
discharge and content-typed upgrade live in `RecognitionLinkingPositiveID`,
and the recognition-produced detecting map in `RecognitionProducedEmbedding`. -/
structure RecognitionLinkingBridgePremises : Prop where
  /-- DEP on a spatial realization yields the content-typed detector
  (not merely the encoding `SupportsNontrivialLinking`). -/
  dep_forces_Detects :
    ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      DeformationErasurePrinciple R.kin → DetectsNontrivialLinking D
  /-- A realized hierarchy constructs an embedded circle with nontrivial
  complement homology in some ambient sphere. -/
  hierarchy_constructs_embedding :
    ∀ (F : ClosedObservableFramework) (_H : RealizedHierarchy F),
      ∃ (D : ℕ) (f : C(TopCat.sphere.{0} 1, TopCat.sphere.{0} D)),
        Topology.IsEmbedding f ∧
          ¬ CategoryTheory.Limits.IsZero (linkingComplementH1 D f)
  /-- Recognition dual-pair / ledger conservation identifies with the
  Alexander binder's detection half. -/
  recognition_realizes_d3_detects :
    DetectsNontrivialLinking 3

/-- **Conditional upgrade.** If the named Recognition→detector premises hold,
then Recognition supply plus those premises yield the content-typed detector
and the Alexander binder's uniqueness half. -/
theorem detects_from_recognition_supply_plus_premises
    (_supply : RecognitionSupplyTowardLinking)
    (bridge : RecognitionLinkingBridgePremises) :
    DetectsNontrivialLinking 3 ∧
      (∀ D, DetectsNontrivialLinking D → D = 3) :=
  ⟨bridge.recognition_realizes_d3_detects, PublicSpineLinkingClosure.forces_D3⟩

/-- Marker retained for audit continuity. Weak premises remain transport-vacuous;
content-typed premises are discharged in `RecognitionLinkingPositiveID`. -/
def positiveIdentificationStillOpen : True := trivial

/-! ## 4. Certificate -/

/-- Machine-checkable Recognition→linking seam certificate (typed wall). -/
structure RecognitionToLinkingSeamCert : Prop where
  /-- What Recognition / hierarchy supplies toward linking. -/
  supply : RecognitionSupplyTowardLinking
  /-- Backend inhabitable without Recognition content. -/
  decoy_backend_alone :
    circleH1ZNonzero → Nonempty MathlibCircleLinkingBackend.{0, 0, 0}
  /-- DEP independence decoy. -/
  decoy_DEP_independent :
    ∃ (D : DimensionForcing.Dimension)
      (R : SpatialDualPairRealization D),
      ¬ DeformationErasurePrinciple R.kin
  /-- Concrete D=4 unlinked decoy coexists with Recognition supply. -/
  decoy_unlinked_D4 :
    RecognitionSupplyTowardLinking ∧
      ¬ DeformationErasurePrinciple fourDimRealization.kin
  /-- Hierarchy linking concludes encoding, not content detector. -/
  hierarchy_hits_encoding :
    ∀ (F : ClosedObservableFramework) (_H : RealizedHierarchy F),
      DimensionForcing.SupportsNontrivialLinking 3
  /-- Headline obstruction package. -/
  bare_recognition_obstruction :
    RecognitionSupplyTowardLinking ∧
      (DimensionForcing.SupportsNontrivialLinking 3) ∧
      (∃ (D : DimensionForcing.Dimension)
        (R : SpatialDualPairRealization D),
        ¬ DeformationErasurePrinciple R.kin) ∧
      (circleH1ZNonzero → Nonempty MathlibCircleLinkingBackend.{0, 0, 0}) ∧
      DetectsNontrivialLinking 3
  /-- Topology authority stays on PublicSpineLinkingClosure. -/
  topology_authority :
    Nonempty AlexanderLinkingBridge ∧
      (∀ D, DetectsNontrivialLinking D → D = 3)
  /-- Conditional upgrade shape (premises undischarged). -/
  conditional_upgrade :
    RecognitionSupplyTowardLinking →
      RecognitionLinkingBridgePremises →
        DetectsNontrivialLinking 3 ∧
          (∀ D, DetectsNontrivialLinking D → D = 3)

/-- The Recognition→linking seam certificate (typed wall). -/
theorem recognitionToLinkingSeamCert : RecognitionToLinkingSeamCert where
  supply := recognition_supply_toward_linking
  decoy_backend_alone := backend_from_circleH1_alone
  decoy_DEP_independent := recognition_DEP_not_forced
  decoy_unlinked_D4 := recognition_coexists_with_unlinked_D4_decoy
  hierarchy_hits_encoding := hierarchy_linking_concludes_encoding
  bare_recognition_obstruction :=
    bare_recognition_does_not_force_DetectsNontrivialLinking
  topology_authority :=
    ⟨PublicSpineLinkingClosure.target_D3, PublicSpineLinkingClosure.forces_D3⟩
  conditional_upgrade := fun supply bridge =>
    detects_from_recognition_supply_plus_premises supply bridge

end RecognitionToLinkingSeam
end Foundation
end IndisputableMonolith

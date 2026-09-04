import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5Ledger
import IndisputableMonolith.RecogGeom.Recognizer

/-!
# Cutset, row 5 (record / D = 3): the space of placements is a recognition
# geometry, and that is RG2

## What this module replaces

`CutsetRow5Ledger` closes D = 3 along a ledger reading whose one content
clause is `posted : read pair ≠ read split` ("space keeps the record of the
act"). That clause is not forced by the ledger
(`LinkingNecessity.dep_not_forced_by_realization_layer`): a ledger may read
every placement of the two loops as one state and keep its records in cells.

This module moves the content clause off the act and onto space. Recognition
Geometry (RecogGeom, the Lean of the published paper) says what space is: a
configuration space together with a recognizer, and axiom RG2 says the
recognizer is nontrivial, some two configurations read as different events
(`RecogGeom.Recognizer.nontrivial`). Applied to the placements of the two
loops, with "recognition-free motion reads the same event" as the invariance
clause, RG2 says: some two placements are told apart. Nothing is said about
the act's own placement, and nothing about a dimension.

## The theorems

* `recognitionGeometry_iff_two_classes`: the placements carry a nontrivial
  invariant recognizer iff some two placements are not joined by a
  recognition-free motion. Pure logic on the kinematics.
* `recognitionGeometry_forces_D3`: on a spatial loop space in dimension `D`
  (the census identification: two placements not joined by a motion exist iff
  `D` supports nontrivial circle linking), a recognition geometry on the
  placements forces `D = 3`.
* `no_recognitionGeometry_off_three`: off three, every invariant recognizer
  on placements is trivial. The placements of two loops are not a recognition
  geometry: there is no space of loop placements there, in the published
  sense of "space".
* `recognitionGeometry_at_three`: at three a recognition geometry exists.
* `d4_not_recognitionGeometry`: the four-dimensional decoy (total deformation)
  admits no invariant recognizer at all.
* `recognitionGeometry_of_ledgerRealized`: the ledger reading of
  `CutsetRow5Ledger` is an invariant recognizer, so the earlier blade implies
  this one; the converse needs no `pair`/`split` at all.

## What is and is not claimed

The escape in the earlier blade, "read every placement as one state", is
exactly the trivial recognizer, and RG2 excludes it by axiom. So the content
clause now reads: the placements of the ledger's traces form a recognition
geometry. That is the published account of what space is, applied to the
traces; it is an identification (MODEL: this is what "space" means in RS), not
a theorem of the ledger. Given it, `D = 3` is a theorem and every other
dimension is a world in which the placements of two loops form no space.

The invariance clause (recognition-free motion = ambient isotopy through
disjoint placements) remains the setting of the linking requirement, as in the
paper.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row5RecogGeom

open LinkingNecessity
open Row5Ledger

/-! ## Invariant recognizers on placements -/

/-- A recognizer on the placements of a pair kinematics (RecogGeom RG2:
nontrivial) that reads the same event along every recognition-free motion. -/
structure InvariantRecognizer (X : PairKinematics) (E : Type) extends
    RecogGeom.Recognizer X.Config E where
  /-- A motion in which nothing is recognized changes no event. -/
  invariant : ∀ a b, X.deform a b → R a = R b

/-- **RG2 on placements.** The placements of the two loops form a recognition
geometry: some invariant recognizer tells two placements apart. -/
def RecognitionGeometry (X : PairKinematics) : Prop :=
  ∃ E : Type, Nonempty (InvariantRecognizer X E)

/-! ## The cut: RG2 is "two motion classes" -/

theorem two_classes_of_recognitionGeometry {X : PairKinematics}
    (h : RecognitionGeometry X) : ∃ a b : X.Config, ¬ X.deform a b := by
  obtain ⟨E, ⟨R⟩⟩ := h
  obtain ⟨a, b, hne⟩ := R.nontrivial
  exact ⟨a, b, fun hd => hne (R.invariant a b hd)⟩

/-- Two placements no motion joins give a one-bit recognizer: "in the motion
class of the first". -/
theorem recognitionGeometry_of_two_classes {X : PairKinematics}
    (h : ∃ a b : X.Config, ¬ X.deform a b) : RecognitionGeometry X := by
  classical
  obtain ⟨a, b, hab⟩ := h
  refine ⟨Bool, ⟨{ R := fun c => decide (X.deform a c)
                   nontrivial := ⟨a, b, ?_⟩
                   invariant := ?_ }⟩⟩
  · have h1 : decide (X.deform a a) = true := decide_eq_true (X.deform_refl a)
    have h2 : decide (X.deform a b) = false := decide_eq_false hab
    rw [h1, h2]; decide
  · intro c d hcd
    have : X.deform a c ↔ X.deform a d :=
      ⟨fun h => X.deform_trans h hcd, fun h => X.deform_trans h (X.deform_symm hcd)⟩
    exact decide_eq_decide.mpr this

theorem recognitionGeometry_iff_two_classes (X : PairKinematics) :
    RecognitionGeometry X ↔ ∃ a b : X.Config, ¬ X.deform a b :=
  ⟨two_classes_of_recognitionGeometry, recognitionGeometry_of_two_classes⟩

/-! ## The earlier blade implies this one -/

/-- A ledger reading is an invariant recognizer into ledger states. -/
def InvariantRecognizer.ofLedgerReading {X : PairKinematics} {D : ℕ}
    (r : LedgerReading X D) : InvariantRecognizer X (State D) where
  R := r.read
  nontrivial := ⟨X.pair, X.split, r.posted⟩
  invariant := fun a b h =>
    (recognitionFree_iff_eq _ _).1 (r.deform_recognitionFree a b h)

theorem recognitionGeometry_of_ledgerRealized {X : PairKinematics}
    (h : LedgerRealized X) : RecognitionGeometry X := by
  obtain ⟨D, ⟨r⟩⟩ := h
  exact ⟨State D, ⟨InvariantRecognizer.ofLedgerReading r⟩⟩

/-- DEP (the act's pair is a posted distinction) implies RG2 on placements; RG2
does not name the act's pair at all. -/
theorem recognitionGeometry_of_dep {X : PairKinematics}
    (h : DeformationErasurePrinciple X) : RecognitionGeometry X :=
  recognitionGeometry_of_two_classes
    ⟨X.pair, X.split, dep_separates_pair_from_split X h⟩

/-! ## Space -/

/-- A spatial loop space in dimension `D`: placements of two disjoint tame
unknotted circles in `S^D` under isotopy through disjoint placements, with the
census identification (Alexander duality at three, Zeeman/Haefliger unknotting
and general position at four and up, Schoenflies at two): two placements no
motion joins exist exactly when `D` supports nontrivial circle linking. -/
structure SpatialLoopSpace (D : DimensionForcing.Dimension) where
  /-- The placements and their recognition-free motions. -/
  kin : PairKinematics
  /-- The census: a second motion class exists iff `D` supports linking. -/
  two_classes_iff :
    (∃ a b : kin.Config, ¬ kin.deform a b) ↔ DimensionForcing.SupportsNontrivialLinking D

/-- **A recognition geometry on loop placements lives in three dimensions.** -/
theorem recognitionGeometry_forces_D3 (D : DimensionForcing.Dimension)
    (S : SpatialLoopSpace D) (h : RecognitionGeometry S.kin) : D = 3 :=
  DimensionForcing.linking_requires_D3 D
    (S.two_classes_iff.1 (two_classes_of_recognitionGeometry h))

/-- **Off three there is no space of loop placements**: every invariant
recognizer is trivial, so RG2 fails and the placements are not a recognition
geometry. -/
theorem no_recognitionGeometry_off_three (D : DimensionForcing.Dimension)
    (hD : D ≠ 3) (S : SpatialLoopSpace D) : ¬ RecognitionGeometry S.kin :=
  fun h => hD (recognitionGeometry_forces_D3 D S h)

/-- At three the placements do form a recognition geometry. -/
theorem recognitionGeometry_at_three (S : SpatialLoopSpace 3) :
    RecognitionGeometry S.kin :=
  recognitionGeometry_of_two_classes
    (S.two_classes_iff.2 DimensionForcing.D3_has_linking)

/-- Every invariant recognizer on a spatial loop space off three is constant. -/
theorem invariantRecognizer_constant_off_three (D : DimensionForcing.Dimension)
    (hD : D ≠ 3) (S : SpatialLoopSpace D) {E : Type}
    (R : RecogGeom.Recognizer S.kin.Config E)
    (hinv : ∀ a b, S.kin.deform a b → R.R a = R.R b) :
    ∀ a b, R.R a = R.R b := by
  intro a b
  by_contra hne
  exact no_recognitionGeometry_off_three D hD S
    ⟨E, ⟨{ R := R.R, nontrivial := R.nontrivial, invariant := hinv }⟩⟩

/-! ## The decoy -/

/-- The four-dimensional decoy: every placement moves to every other. -/
def fourDimLoopSpace : SpatialLoopSpace 4 where
  kin := unlinkedKinematics
  two_classes_iff := by
    constructor
    · rintro ⟨a, b, hab⟩
      exact absurd trivial hab
    · intro h
      exact absurd h DimensionForcing.D4_no_linking

/-- The decoy admits no invariant recognizer: the placements of two loops in
four dimensions carry no recognizable distinction at all. -/
theorem d4_not_recognitionGeometry : ¬ RecognitionGeometry unlinkedKinematics :=
  fun h => by
    obtain ⟨a, b, hab⟩ := two_classes_of_recognitionGeometry h
    exact hab trivial

/-! ## Certificate -/

structure Cert : Prop where
  iff_two_classes : ∀ X : PairKinematics,
    RecognitionGeometry X ↔ ∃ a b : X.Config, ¬ X.deform a b
  forces : ∀ (D : DimensionForcing.Dimension) (S : SpatialLoopSpace D),
    RecognitionGeometry S.kin → D = 3
  off_three : ∀ (D : DimensionForcing.Dimension), D ≠ 3 →
    ∀ S : SpatialLoopSpace D, ¬ RecognitionGeometry S.kin
  at_three : ∀ S : SpatialLoopSpace 3, RecognitionGeometry S.kin
  ledger_reading_implies : ∀ X : PairKinematics, LedgerRealized X → RecognitionGeometry X
  decoy : ¬ RecognitionGeometry unlinkedKinematics

theorem cert : Cert where
  iff_two_classes := recognitionGeometry_iff_two_classes
  forces := recognitionGeometry_forces_D3
  off_three := no_recognitionGeometry_off_three
  at_three := recognitionGeometry_at_three
  ledger_reading_implies := fun _ h => recognitionGeometry_of_ledgerRealized h
  decoy := d4_not_recognitionGeometry

end Row5RecogGeom
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith

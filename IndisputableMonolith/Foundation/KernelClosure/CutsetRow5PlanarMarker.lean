import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5RecogGeom

/-!
# Cutset, row 5: the planar decoy, or why the ambient is a sphere

## The objection (Philip, theory-discussion, 2026-09-03)

"If we are lifting the loops onto R^D rather than S^D, there is a topological
invariant for separate loops in D = 2: nesting. The usage of S^D for the space
in which the loops are embedded is what kills D = 2 (nesting versus disjoint is
not defined on S^2 while it is on R^2), not the requirement of any topological
invariant for simple loops in a D space."

He is right about the mathematics, and the paper had presented the sphere as a
convention. This module formalizes the objection at the level of the paper's
kinematics and proves what the sphere actually encodes.

## The one topological input

Two disjoint circles `A`, `B` on `S^2` cut it into three regions (Jordan and
Schoenflies): the disk bounded by `A` away from `B`, the annulus between the
circles, and the disk bounded by `B` away from `A`. The plane `R^2` is `S^2`
with one point marked and removed. The planar nesting relation of `A` and `B`
is a function of which region holds the marked point: mark the `A`-disk and `B`
lies inside `A`; mark the annulus and the circles sit side by side; mark the
`B`-disk and `A` lies inside `B` (`nestingOf`). So nesting is a relation among
three objects, two loops and a point, read as a relation between two.

(The same fact in homology: `H̃₁(S² \ A) = 0`, while `H̃₁(R² \ A) = H̃₁(S² \
(A ∪ {∞})) ≅ H̃⁰(S¹ ⊔ pt) ≅ ℤ`. The planar winding number of `B` about `A` is
the Alexander dual of the marked point. In `D = 3` the two agree, `ℤ` and `ℤ`;
in `D ≥ 4` both vanish. `D = 2` is the only dimension where the plane and the
sphere disagree, and the disagreement is exactly the marked point.)

## Two kinematics on the same configurations

The configuration is the region holding the marked point.

* `heldMarker`: the marked point is held, so regions are motion classes. This is
  the plane with its point at infinity. It satisfies the abstract linking
  requirement (DEP) through nesting (`heldMarker_dep`). That is the loophole,
  formal: the requirement alone does not kill `D = 2`.
* `freeMarker`: the marked point is not a recognized object, so a motion may
  carry it across either circle with no post, and all regions are one class.
  Nesting is not a pairing observable there (`nesting_not_invariant_of_free`),
  DEP fails (`freeMarker_not_dep`), no invariant recognizer exists
  (`freeMarker_not_recognitionGeometry`), and the kinematics is a legitimate
  `SpatialLoopSpace 2` (`planarFreeLoopSpace`), consistent with the census.

## The repair

`heldMarker_ne_spatial`: no spatial loop space in dimension two has the
held-marker kinematics, because that kinematics has two motion classes and
`S^2` admits no circle linking. So the paper's sphere is not a convention. It is
the statement that the placement is read from the two loops alone, with no third
marked object, which is what the linking requirement of the ledger paper asks
(a pairwise invariant of the two curves the recognizer runs). Nesting is a
record kept by three things, two loops and a point neither loop produced. A
world that supplies such a point can keep a record in `D = 2`; a world in which
the two loops alone keep it has `D = 3`.

Tag: MODEL. The three-region identification is the topological input, taken as
the definition of the configuration type; everything below it is proved.
Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row5PlanarMarker

open LinkingNecessity
open Row5RecogGeom

/-! ## Regions and the planar reading -/

/-- The three regions of `S^2` minus two disjoint circles `A`, `B`. -/
inductive Region
  /-- The disk bounded by `A` that does not contain `B`. -/
  | insideA
  /-- The annulus between the two circles. -/
  | between
  /-- The disk bounded by `B` that does not contain `A`. -/
  | insideB
  deriving DecidableEq, Repr

/-- The planar nesting relation of two disjoint circles. -/
inductive Nesting
  /-- `B` lies in the bounded component of `R² \ A`. -/
  | bInsideA
  /-- Each circle lies in the unbounded component of the other's complement. -/
  | sideBySide
  /-- `A` lies in the bounded component of `R² \ B`. -/
  | aInsideB
  deriving DecidableEq, Repr

/-- Remove the marked point from `S^2` and read the plane: the circle whose disk
holds the marked point becomes the outer one. Nesting is a function of the
marked point's region. -/
def nestingOf : Region → Nesting
  | .insideA => .bInsideA
  | .between => .sideBySide
  | .insideB => .aInsideB

/-- Every planar nesting relation is realized by exactly one region of the
marked point: the marked point carries all of the nesting information. -/
theorem nestingOf_injective : Function.Injective nestingOf := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem nestingOf_surjective : Function.Surjective nestingOf := by
  intro n
  cases n
  · exact ⟨.insideA, rfl⟩
  · exact ⟨.between, rfl⟩
  · exact ⟨.insideB, rfl⟩

/-! ## The two kinematics -/

/-- The plane with its point at infinity held fixed: regions are motion
classes. The posted placement is "the record encloses the act" (marked point in
the `A`-disk, so `B` is inside `A`); the separated placement is side by side. -/
@[reducible] def heldMarker : PairKinematics where
  Config := Region
  deform := fun a b => a = b
  deform_refl := fun _ => rfl
  deform_symm := fun h => h.symm
  deform_trans := fun h₁ h₂ => h₁.trans h₂
  split := .between
  pair := .insideA

/-- The marked point is not a recognized object: a motion may carry it across
either circle with no post, so every region reaches every other. Same posted
and separated placements as `heldMarker`. -/
@[reducible] def freeMarker : PairKinematics where
  Config := Region
  deform := fun _ _ => True
  deform_refl := fun _ => trivial
  deform_symm := fun _ => trivial
  deform_trans := fun _ _ => trivial
  split := .between
  pair := .insideA

/-! ## The loophole, formal -/

/-- Nesting as an integer pairing on the held-marker plane: `1` when the
circles are nested either way, `0` when side by side. -/
def nestingPairing : PairingObservable heldMarker where
  pairing := fun r => if r = Region.between then 0 else 1
  deform_invariant := fun a b h => by
    change a = b at h
    subst h
    rfl
  split_zero := by decide

/-- **The loophole.** On the plane with a held point at infinity, the abstract
linking requirement holds in dimension two: the posted (nested) placement
carries nonzero pairing and no motion carries it to the separated one. The
requirement alone does not kill `D = 2`. -/
theorem heldMarker_dep : DeformationErasurePrinciple heldMarker :=
  ⟨nestingPairing, by decide⟩

/-- The held-marker plane has two motion classes: nested and side by side. -/
theorem heldMarker_two_classes :
    ∃ a b : heldMarker.Config, ¬ heldMarker.deform a b :=
  ⟨.insideA, .between, by decide⟩

/-- The held-marker plane is a recognition geometry in the paper's sense:
nesting is an invariant recognizer. -/
theorem heldMarker_recognitionGeometry : RecognitionGeometry heldMarker :=
  recognitionGeometry_of_two_classes heldMarker_two_classes

/-! ## What the marked point is doing -/

/-- Nesting is not a pairing observable once the marked point is free: a motion
that posts nothing carries a nested placement to a side-by-side one. -/
theorem nesting_not_invariant_of_free :
    ∃ a b : freeMarker.Config, freeMarker.deform a b ∧ nestingOf a ≠ nestingOf b :=
  ⟨.insideA, .between, trivial, by decide⟩

/-- On the free-marker plane every pairing observable vanishes identically. -/
theorem freeMarker_pairings_zero (P : PairingObservable freeMarker) (c : Region) :
    P.pairing c = 0 := by
  have h := P.deform_invariant c freeMarker.split trivial
  rw [h]
  exact P.split_zero

/-- With the marked point free, the linking requirement fails in dimension two,
as the census says it must. -/
theorem freeMarker_not_dep : ¬ DeformationErasurePrinciple freeMarker := by
  rintro ⟨P, hP⟩
  exact hP (freeMarker_pairings_zero P _)

/-- With the marked point free, no invariant recognizer tells two placements
apart: the placements of two loops in the plane form no space. -/
theorem freeMarker_not_recognitionGeometry : ¬ RecognitionGeometry freeMarker :=
  fun h => by
    obtain ⟨a, b, hab⟩ := two_classes_of_recognitionGeometry h
    exact hab trivial

/-- The free-marker plane is a legitimate spatial loop space in dimension two:
one motion class, and `S^2` admits no circle linking. -/
def planarFreeLoopSpace : SpatialLoopSpace 2 where
  kin := freeMarker
  two_classes_iff := by
    constructor
    · rintro ⟨a, b, hab⟩
      exact absurd trivial hab
    · intro h
      exact absurd h DimensionForcing.D2_no_linking

/-! ## The repair -/

/-- Every spatial loop space in dimension two has one motion class. -/
theorem spatial_two_one_class (S : SpatialLoopSpace 2) (a b : S.kin.Config) :
    S.kin.deform a b := by
  by_contra h
  exact DimensionForcing.D2_no_linking (S.two_classes_iff.1 ⟨a, b, h⟩)

/-- **The repair.** No spatial loop space in dimension two is the held-marker
plane. The held marker adds exactly one distinction, nesting, and that
distinction belongs to two loops and a point, not to two loops. The paper's
sphere is the statement that the placement is read from the two loops alone. -/
theorem heldMarker_ne_spatial (S : SpatialLoopSpace 2) : S.kin ≠ heldMarker := by
  intro h
  obtain ⟨a, b, hab⟩ := heldMarker_two_classes
  have hone : ∀ x y : heldMarker.Config, heldMarker.deform x y := by
    rw [← h]
    exact spatial_two_one_class S
  exact hab (hone a b)

/-- Two loops plus a held marked point is a recognition geometry in dimension
two; two loops alone is not. The difference is the marked point and nothing
else: the configurations are the same type, and the two kinematics differ only
in whether a motion may move the marker. -/
theorem marker_is_the_difference :
    RecognitionGeometry heldMarker ∧ ¬ RecognitionGeometry freeMarker ∧
      heldMarker.Config = freeMarker.Config ∧
      heldMarker.pair = freeMarker.pair ∧ heldMarker.split = freeMarker.split :=
  ⟨heldMarker_recognitionGeometry, freeMarker_not_recognitionGeometry, rfl, rfl, rfl⟩

/-! ## Certificate -/

structure Cert : Prop where
  loophole : DeformationErasurePrinciple heldMarker
  loophole_is_geometry : RecognitionGeometry heldMarker
  nesting_needs_marker :
    ∃ a b : freeMarker.Config, freeMarker.deform a b ∧ nestingOf a ≠ nestingOf b
  free_not_dep : ¬ DeformationErasurePrinciple freeMarker
  free_not_geometry : ¬ RecognitionGeometry freeMarker
  free_is_spatial : ∃ S : SpatialLoopSpace 2, S.kin = freeMarker
  held_not_spatial : ∀ S : SpatialLoopSpace 2, S.kin ≠ heldMarker
  marker_carries_nesting : Function.Bijective nestingOf

theorem cert : Cert where
  loophole := heldMarker_dep
  loophole_is_geometry := heldMarker_recognitionGeometry
  nesting_needs_marker := nesting_not_invariant_of_free
  free_not_dep := freeMarker_not_dep
  free_not_geometry := freeMarker_not_recognitionGeometry
  free_is_spatial := ⟨planarFreeLoopSpace, rfl⟩
  held_not_spatial := heldMarker_ne_spatial
  marker_carries_nesting := ⟨nestingOf_injective, nestingOf_surjective⟩

end Row5PlanarMarker
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith

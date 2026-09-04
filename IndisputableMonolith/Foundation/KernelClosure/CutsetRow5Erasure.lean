import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness
import IndisputableMonolith.Foundation.LinkingNecessity

/-!
# Row 5 by cutset: the posting is a record

Row 5 of the kernel purchase ledger is linking detection, priced at the
deformation-erasure principle (DEP): some spatial dual-pair realization admits
a pairing observable that does not vanish on the posted pair. Countermodel:
`fourDimRealization`, whose kinematics deforms everything to everything.

## Fail-fast, measured

B3 (`IsRecord`) read literally on the two census objects:

* `D = 3` (`windingPairKinematics`, `deform := Eq`): every configuration is a
  record; `HasRecords` holds (`d3_pair_is_record`).
* `D = 4` (`unlinkedKinematics`, `deform := True`): no configuration is a
  record; `HasRecords` fails (`d4_has_no_records`, via
  `no_records_of_everything_moves`). The unlinked world is not a ledger.

So the literal blade separates the census pair; no re-reading was needed.

## What DEP says, extensionally

`dep_iff_not_deform_pair_split`: DEP holds exactly when no recognition-free
deformation carries the posted pair to the split. The forward direction is
`dep_separates_pair_from_split`; the converse builds the indicator observable
"is deformation-reachable from the posted pair" (deformation-invariant because
deformation is an equivalence; zero on the split by hypothesis). No sector is
assigned by hand; the observable is read off the kinematics.

## The row

Floor: a posting is a distinction, `pair ≠ split` (T-2 transported to
configurations). Blade: the posted pair is a record, `IsRecord deform pair`
(B3 at the posting; a definition of what a ledger keeps). Sentence: DEP.
Exclusion (`dep_of_record_posting`): a record that is a distinction cannot
deform to the split, so DEP holds. `row` inhabits the harness with the `D = 3`
kinematics as real object and the unlinked kinematics as violator.

Shape: a **cut**, not a merge. The blade is strictly stronger than the
sentence: the parity kinematics (`parityKinematics`) satisfies DEP and fails the
blade (`parity_dep_but_not_record`). Dichotomy to nondegenerate in row 2a has
the same shape.

Consequence for the dimension: `record_posting_forces_D3`. If a spatial
realization's posted pair is a record and a distinction, its ambient dimension
is three. The ledger row moves from PURCHASE to MODEL under "the posting is a
record"; the D = 4 realization is excluded not by fiat but because it keeps no
record at all.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row5Erasure

open LinkingNecessity LinkingFromHierarchy HierarchyRealization ClosedFramework

/-! ## Fail-fast: B3 on the census pair -/

/-- `D = 3`: the posted pair is a record (every winding class is). -/
theorem d3_pair_is_record (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    IsRecord (windingPairKinematics F H).deform (windingPairKinematics F H).pair :=
  fun _ h => h.symm

theorem d3_has_records (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    HasRecords (windingPairKinematics F H).deform :=
  ⟨_, d3_pair_is_record F H⟩

/-- `D = 4`: the unlinked world keeps no record. -/
theorem d4_has_no_records : ¬ HasRecords unlinkedKinematics.deform :=
  no_records_of_everything_moves _ (fun c : ℤ => ⟨c + 1, trivial, (lt_add_one c).ne'⟩)

theorem d4_pair_not_record : ¬ IsRecord unlinkedKinematics.deform unlinkedKinematics.pair :=
  fun h => d4_has_no_records ⟨_, h⟩

/-! ## DEP, extensionally -/

/-- **DEP is "the posted pair does not deform to the split".** -/
theorem dep_iff_not_deform_pair_split (X : PairKinematics) :
    DeformationErasurePrinciple X ↔ ¬ X.deform X.pair X.split := by
  constructor
  · exact dep_separates_pair_from_split X
  · intro hns
    classical
    refine ⟨⟨fun c => if X.deform X.pair c then 1 else 0, ?_, ?_⟩, ?_⟩
    · intro a b hab
      show (if X.deform X.pair a then (1 : ℤ) else 0) = (if X.deform X.pair b then 1 else 0)
      by_cases ha : X.deform X.pair a
      · rw [if_pos ha, if_pos (X.deform_trans ha hab)]
      · rw [if_neg ha, if_neg (fun hb => ha (X.deform_trans hb (X.deform_symm hab)))]
    · exact if_neg hns
    · simp [X.deform_refl]

/-! ## The exclusion -/

/-- **A posted record that is a distinction satisfies DEP.** -/
theorem dep_of_record_posting (X : PairKinematics) (hne : X.pair ≠ X.split)
    (hrec : IsRecord X.deform X.pair) : DeformationErasurePrinciple X :=
  (dep_iff_not_deform_pair_split X).2 (fun h => hne (hrec _ h).symm)

/-- The blade is strictly stronger than the sentence: the parity kinematics. -/
@[reducible] def parityKinematics : PairKinematics where
  Config := ℤ
  deform := fun a b => a % 2 = b % 2
  deform_refl := fun _ => rfl
  deform_symm := Eq.symm
  deform_trans := Eq.trans
  split := 0
  pair := 1

theorem parity_dep_but_not_record :
    DeformationErasurePrinciple parityKinematics ∧
      ¬ IsRecord parityKinematics.deform parityKinematics.pair := by
  refine ⟨(dep_iff_not_deform_pair_split _).2 (by decide), ?_⟩
  intro h
  have := h 3 (by decide)
  norm_num at this

/-! ## The row -/

/-- Row 5 in harness form, on pair kinematics. -/
noncomputable def row : CutsetRow PairKinematics where
  Floor := fun X => X.pair ≠ X.split
  Sentence := DeformationErasurePrinciple
  Blade := fun X => IsRecord X.deform X.pair
  provenance := .definition "the posting is a record: recognition-free deformation cannot move it"
  real := windingPairKinematics jRealizedHierarchy.1 jRealizedHierarchy.2
  real_floor := by show (2 : ℤ) ≠ 0; norm_num
  blade_real := d3_pair_is_record jRealizedHierarchy.1 jRealizedHierarchy.2
  violator := unlinkedKinematics
  violator_floor := by show (2 : ℤ) ≠ 0; norm_num
  violator_violates := unlinkedKinematics_refutes_dep
  blade_kills_violator := d4_pair_not_record
  exclusion := fun X hne hs hb => hs (dep_of_record_posting X hne hb)

/-! ## The dimension -/

/-- **A recorded posting lives in three dimensions.** -/
theorem record_posting_forces_D3 (D : DimensionForcing.Dimension)
    (R : SpatialDualPairRealization D)
    (hne : R.kin.pair ≠ R.kin.split) (hrec : IsRecord R.kin.deform R.kin.pair) :
    D = 3 :=
  dep_forces_D3 D R (dep_of_record_posting R.kin hne hrec)

/-! ## Certificate -/

structure Cert : Prop where
  d3_records : ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
    HasRecords (windingPairKinematics F H).deform
  d4_no_records : ¬ HasRecords unlinkedKinematics.deform
  dep_extensional : ∀ X : PairKinematics, DeformationErasurePrinciple X ↔ ¬ X.deform X.pair X.split
  exclusion : ∀ X : PairKinematics, X.pair ≠ X.split → IsRecord X.deform X.pair →
    DeformationErasurePrinciple X
  strict : DeformationErasurePrinciple parityKinematics ∧
    ¬ IsRecord parityKinematics.deform parityKinematics.pair
  row_forces : ∀ X, row.Floor X → row.Blade X → row.Sentence X
  row_class_nonempty : ∃ X, row.Floor X ∧ ¬ row.Sentence X
  forces_D3 : ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
    R.kin.pair ≠ R.kin.split → IsRecord R.kin.deform R.kin.pair → D = 3

theorem cert : Cert where
  d3_records := d3_has_records
  d4_no_records := d4_has_no_records
  dep_extensional := dep_iff_not_deform_pair_split
  exclusion := dep_of_record_posting
  strict := parity_dep_but_not_record
  row_forces := row.forces
  row_class_nonempty := row.class_nonempty
  forces_D3 := record_posting_forces_D3

end Row5Erasure
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith

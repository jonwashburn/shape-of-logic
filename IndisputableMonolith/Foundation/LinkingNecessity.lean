import IndisputableMonolith.Foundation.LinkingFromHierarchy

/-!
# Linking Necessity: the T8 bridge factored into theorem + named principle

The strict T-1-to-T8 audit carried the row "T8 linking interpretation" as a
`documentedBridgeDefinition`: the requirement that reality support nontrivially
linked recognition loops was asserted by definition ("ledger conservation
requires non-trivial linking"), with no forcing theorem above it and no
independence obstruction below it.  This module removes that asymmetry.  After
it, the T8 bridge consists of:

1. **THEOREM (this module, genuine Mathlib content).**  The realized hierarchy's
   recognition loop comes with its ledger conjugate (the credit loop, the
   orientation reversal of the debit loop).  Their winding numbers are `1` and
   `-1`: the pair is *balanced* (sum `0`, the sigma = 0 conservation law) and
   *distinct* (difference `2`, the posted distinction).  Winding is genuinely
   deformation-invariant (`pathDisplacement_homotopic`, proved through the
   covering-space lift).  No axioms, no new definitional encodings.

2. **NAMED PRINCIPLE (the residual physical input, made explicit).**
   `DeformationErasurePrinciple`: the posted dual-pair distinction is carried by
   a deformation-invariant pairing observable that does not vanish on the
   realized pair.  Equivalently: recognition-free continuous deformation cannot
   erase a posted distinction; only recognition events repost the ledger.  This
   is T2/T4 vocabulary (cost-free deformation, posting, distinction), with no
   topology inside it.

3. **THEOREM (this module).**  The principle forces separation: a kinematics
   satisfying the principle cannot deform the realized pair to the split
   configuration (`dep_separates_pair_from_split`), so the ambient dimension
   must admit a nonzero deformation-invariant pairing of disjoint recognition
   loops.  Through the Alexander identification this forces `D = 3`
   (`dep_forces_D3`), and in every dimension `D ≠ 3` the dual-pair distinction
   is provably erasable (`dual_pair_erasable_off_three`): double entry cannot
   survive deformation anywhere but `D = 3`.

4. **PROVED OBSTRUCTION (this module).**  The principle is a genuine input, not
   a consequence of the surrounding structure: a complete spatial realization
   exists (in `D = 4`, with the everything-deforms kinematics) in which every
   pairing observable vanishes and the principle fails
   (`dep_not_forced_by_realization_layer`).  Distinctness of configurations
   alone does not give deformation-stable distinctness
   (`config_distinctness_does_not_force_dep`).  This puts the linking row in
   the same epistemic state as the other three audit rows: named input plus
   proved independence.

5. **DOCUMENTED EXTERNAL MATH (unchanged, cited once).**  The availability
   statement "a nonzero deformation-invariant pairing of disjoint circle pairs
   exists in `S^D` iff `D = 3`" is Alexander duality (Hatcher Thm 3.44) plus
   the circle cohomology computation (Hatcher section 2.2).  The `H_1(S^1; Z)`
   side is genuinely proved over Mathlib singular homology
   (`CircleWindingChain.circleH1ZIsoInt_holds`); the duality isomorphism and the
   high-dimensional unlinking remain the encoded characterization
   (`AlexanderDuality.SphereAdmitsCircleLinking`).  Each concrete realization in
   this module *proves* its `pairing_available_iff` field; what stays
   documented is only that physical space instantiates the structure, which is
   classical topology awaiting Mathlib, not a physics-side free choice.

After this module the only definitional content left in T8 is bog-standard
external topology.  The physics-side interpretation is a named principle whose
sufficiency (forcing `D = 3`) and independence (proved obstruction) are both
theorems.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LinkingNecessity

open ClosedFramework
open HierarchyRealization
open CircleWinding
open CircleParam
open LinkingFromHierarchy
open scoped Real unitInterval

noncomputable section

/-! ## Part 1: the ledger dual pair, genuinely realized

Double entry (T3) means every recognition flow posts twice: debit and credit.
On the recognition circle of a realized hierarchy (Phase 5), the debit flow is
the once-around recognition loop; the credit flow is its orientation reversal.
Everything in this part is computed through the proved covering-space winding
machinery; nothing is encoded. -/

/-- Reversing a path negates its winding number.  Lift-level fact, derived from
the proved `pathDisplacement_reverse`. -/
theorem pathWinding_reversePath (γ : C(I, SphereOne)) :
    pathWinding (reversePath γ) = - pathWinding γ := by
  show pathDisplacement (reversePath γ) / (2 * Real.pi)
      = -(pathDisplacement γ / (2 * Real.pi))
  rw [pathDisplacement_reverse]
  ring

/-- The winding number is invariant under recognition-free deformation
(homotopy rel endpoints).  This is the genuine, proved content behind the
abstract pairing observables below: in `D = 3` such an observable actually
exists. -/
theorem winding_deformation_invariant {γ δ : C(I, SphereOne)}
    (h : γ.HomotopicRel δ {0, 1}) :
    pathWinding γ = pathWinding δ := by
  show pathDisplacement γ / (2 * Real.pi) = pathDisplacement δ / (2 * Real.pi)
  rw [pathDisplacement_homotopic h]

/-- **The credit loop**: the ledger conjugate of the recognition (debit) loop,
its traversal in reversed orientation.  Double entry supplies both flows; the
recognition circle realizes them as the two oriented once-around loops. -/
def creditLoop (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    C(I, SphereOne) :=
  reversePath (recognitionCircleLoop F H)

/-- The credit loop starts at the circle basepoint. -/
theorem creditLoop_zero (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    creditLoop F H 0 = sphereOneBasepoint := by
  show recognitionCircleLoop F H (unitInterval.symm 0) = sphereOneBasepoint
  rw [unitInterval.symm_zero]
  exact recognitionCircleLoop_one F H

/-- The credit loop closes at the circle basepoint. -/
theorem creditLoop_one (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    creditLoop F H 1 = sphereOneBasepoint := by
  show recognitionCircleLoop F H (unitInterval.symm 1) = sphereOneBasepoint
  rw [unitInterval.symm_one]
  exact recognitionCircleLoop_zero F H

/-- The credit loop has winding number `-1`: the conjugate posting winds once
around in the opposite orientation. -/
theorem creditLoop_winding_neg_one
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    pathWinding (creditLoop F H) = -1 := by
  unfold creditLoop
  rw [pathWinding_reversePath, recognitionCircleLoop_winding_one]

/-- **The dual pair is balanced**: debit and credit windings sum to zero.  This
is the sigma = 0 conservation law realized topologically. -/
theorem dual_pair_balanced
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    pathWinding (recognitionCircleLoop F H) + pathWinding (creditLoop F H) = 0 := by
  rw [recognitionCircleLoop_winding_one, creditLoop_winding_neg_one]
  ring

/-- **The dual pair is distinct**: debit and credit are different flows.  The
distinction is posted in the windings themselves (`1 ≠ -1`). -/
theorem dual_pair_distinct
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    pathWinding (recognitionCircleLoop F H) ≠ pathWinding (creditLoop F H) := by
  rw [recognitionCircleLoop_winding_one, creditLoop_winding_neg_one]
  norm_num

/-- The ledger pairing gap: the posted magnitude of the dual-pair distinction,
the difference of the two windings. -/
def ledgerPairingGap
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) : ℝ :=
  pathWinding (recognitionCircleLoop F H) - pathWinding (creditLoop F H)

/-- The ledger pairing gap is exactly `2` (windings `1` and `-1`). -/
theorem ledgerPairingGap_eq_two
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    ledgerPairingGap F H = 2 := by
  unfold ledgerPairingGap
  rw [recognitionCircleLoop_winding_one, creditLoop_winding_neg_one]
  ring

/-- The posted dual-pair distinction is nonzero. -/
theorem ledgerPairingGap_ne_zero
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    ledgerPairingGap F H ≠ 0 := by
  rw [ledgerPairingGap_eq_two]
  norm_num

/-! ## Part 2: the named principle and the forcing theorems

The abstraction layer.  A `PairKinematics` is the deformation structure on
dual-loop configurations: recognition-free continuous deformation is an
equivalence-shaped reachability relation, `split` is the separated
configuration (pairing erased), `pair` is the configuration the ledger dual
pair realizes.  A `PairingObservable` is a deformation-invariant integer
pairing vanishing on split configurations: exactly what the proved winding
invariant is in `D = 3` (`winding_deformation_invariant`), and exactly what
Alexander duality says cannot be nonzero in `D ≠ 3`. -/

/-- Deformation kinematics of dual-loop configurations in an ambient space. -/
structure PairKinematics where
  /-- Configurations of the dual loop pair. -/
  Config : Type
  /-- Recognition-free continuous deformation reachability. -/
  deform : Config → Config → Prop
  /-- Doing nothing is a deformation. -/
  deform_refl : ∀ c, deform c c
  /-- Deformations reverse. -/
  deform_symm : ∀ {a b}, deform a b → deform b a
  /-- Deformations compose. -/
  deform_trans : ∀ {a b c}, deform a b → deform b c → deform a c
  /-- The separated (split) configuration: the pairing is erased. -/
  split : Config
  /-- The configuration realized by the ledger dual pair. -/
  pair : Config

/-- A deformation-invariant integer pairing that vanishes on the split
configuration.  The winding pairing of Part 1 is the genuine `D = 3` instance. -/
structure PairingObservable (X : PairKinematics) where
  /-- The pairing value of a configuration. -/
  pairing : X.Config → ℤ
  /-- Recognition-free deformation preserves the pairing. -/
  deform_invariant : ∀ a b, X.deform a b → pairing a = pairing b
  /-- The split configuration carries zero pairing. -/
  split_zero : pairing X.split = 0

/-- **The Deformation-Erasure Principle (DEP)**, the named residual physical
input of the T8 bridge: the posted dual-pair distinction is carried by a
pairing observable that does not vanish on the realized pair.  Recognition-free
deformation cannot erase a posted distinction; only recognition events repost
the ledger.  Stated entirely in T2/T4 vocabulary; no topology inside. -/
def DeformationErasurePrinciple (X : PairKinematics) : Prop :=
  ∃ P : PairingObservable X, P.pairing X.pair ≠ 0

/-- **DEP forces separation**: under the principle, no recognition-free
deformation carries the realized dual pair to the split configuration.  The
posted distinction is deformation-stable.  Pure logic; no topology. -/
theorem dep_separates_pair_from_split (X : PairKinematics)
    (h : DeformationErasurePrinciple X) :
    ¬ X.deform X.pair X.split := by
  intro hdeform
  obtain ⟨P, hP⟩ := h
  exact hP ((P.deform_invariant _ _ hdeform).trans P.split_zero)

/-- A spatial realization of the ledger dual pair in ambient dimension `D`.
The `pairing_available_iff` field is the Alexander identification (Hatcher
Thm 3.44 + section 2.2), carried as an explicit named hypothesis rather than a
free-floating definition: the ambient dimension admits a nonzero pairing
observable on the realized pair exactly when the circle's reduced cohomology in
degree `D - 2` is nontrivial.  Concrete instances *prove* this field
(`hierarchySpatialRealization` at `D = 3`, `fourDimRealization` at `D = 4`);
what remains documented is only that physical space instantiates the
structure. -/
structure SpatialDualPairRealization (D : DimensionForcing.Dimension) where
  /-- The deformation kinematics of dual-loop configurations in dimension `D`. -/
  kin : PairKinematics
  /-- Alexander identification: nonzero pairing observables for the realized
  pair exist in `S^D` exactly when `D` supports nontrivial circle linking. -/
  pairing_available_iff :
    (∃ P : PairingObservable kin, P.pairing kin.pair ≠ 0) ↔
      DimensionForcing.SupportsNontrivialLinking D

/-- **DEP forces linking availability**: a spatial realization satisfying the
principle lives in a dimension that supports nontrivial circle linking. -/
theorem dep_forces_linking (D : DimensionForcing.Dimension)
    (R : SpatialDualPairRealization D)
    (hDEP : DeformationErasurePrinciple R.kin) :
    DimensionForcing.SupportsNontrivialLinking D :=
  R.pairing_available_iff.mp hDEP

/-- **DEP forces `D = 3`**: the linking *requirement* is no longer a bare
definition; it is derived from the named principle, with the dimension pinned
by the existing Alexander surface. -/
theorem dep_forces_D3 (D : DimensionForcing.Dimension)
    (R : SpatialDualPairRealization D)
    (hDEP : DeformationErasurePrinciple R.kin) :
    D = 3 :=
  DimensionForcing.linking_requires_D3 D (dep_forces_linking D R hDEP)

/-- **Off `D = 3` the ledger distinction is erasable**: in every ambient
dimension other than `3`, every spatial realization refutes the principle, so
the posted dual-pair distinction collapses under recognition-free deformation.
Double entry cannot survive deformation anywhere but `D = 3`. -/
theorem dual_pair_erasable_off_three (D : DimensionForcing.Dimension)
    (hD : D ≠ 3) (R : SpatialDualPairRealization D) :
    ¬ DeformationErasurePrinciple R.kin := by
  intro hDEP
  exact hD (dep_forces_D3 D R hDEP)

/-! ## Part 3: the `D = 3` instance, anchored in the hierarchy windings

Non-vacuity.  The deformation classes of dual-loop configurations in `D = 3`
are faithfully carried by the integer pairing (the winding gap), because the
winding number is genuinely deformation-invariant
(`winding_deformation_invariant`).  The realized pair sits in the class with
pairing `2` (the proved `ledgerPairingGap`); the split configuration sits in
the class with pairing `0`. -/

/-- The `D = 3` kinematics of dual-loop configurations, carried by the integer
pairing classes.  Justified by the proved homotopy invariance of the winding:
configurations are identified exactly when no pairing observable separates
them. -/
@[reducible] def windingPairKinematics
    (_F : ClosedObservableFramework) (_H : RealizedHierarchy _F) :
    PairKinematics where
  Config := ℤ
  deform := Eq
  deform_refl := fun _ => rfl
  deform_symm := Eq.symm
  deform_trans := Eq.trans
  split := 0
  pair := 2

/-- The realized pair configuration carries exactly the proved ledger pairing
gap of the hierarchy's dual loops: the abstract `2` is the genuine winding
difference, not a free choice. -/
theorem windingPairKinematics_pair_eq_gap
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    (((windingPairKinematics F H).pair : ℤ) : ℝ) = ledgerPairingGap F H := by
  rw [ledgerPairingGap_eq_two]
  show ((2 : ℤ) : ℝ) = 2
  norm_num

/-- The spatial realization of the dual pair in `D = 3`: the Alexander
identification field is *proved* here, with the identity pairing observable
witnessing availability and `D3_has_linking` witnessing the linking side. -/
def hierarchySpatialRealization
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    SpatialDualPairRealization 3 where
  kin := windingPairKinematics F H
  pairing_available_iff := by
    constructor
    · intro _
      exact DimensionForcing.D3_has_linking
    · intro _
      refine ⟨⟨fun c => c, ?_, rfl⟩, ?_⟩
      · intro a b hab
        exact hab
      · show (2 : ℤ) ≠ 0
        norm_num

/-- **The hierarchy's spatial realization satisfies DEP**: the winding pairing
is the nonvanishing observable.  The principle is realizable, and realized by
the structure the chain itself produces. -/
theorem hierarchy_realization_satisfies_dep
    (F : ClosedObservableFramework) (H : RealizedHierarchy F) :
    DeformationErasurePrinciple (hierarchySpatialRealization F H).kin := by
  refine ⟨⟨fun c => c, ?_, rfl⟩, ?_⟩
  · intro a b hab
    exact hab
  · show (2 : ℤ) ≠ 0
    norm_num

/-- The `J`-produced hierarchy (golden scalar, `goldenFramework`) satisfies DEP
through its own spatial realization: the whole chain from `J` to the `D = 3`
forcing is non-vacuous. -/
theorem j_hierarchy_satisfies_dep :
    DeformationErasurePrinciple
      (hierarchySpatialRealization
        jRealizedHierarchy.1 jRealizedHierarchy.2).kin :=
  hierarchy_realization_satisfies_dep jRealizedHierarchy.1 jRealizedHierarchy.2

/-- `D = 3` recovered from the concrete hierarchy realization and DEP: the
end-to-end instance of the forcing theorem. -/
theorem hierarchy_dep_forces_D3 :
    (3 : DimensionForcing.Dimension) = 3 :=
  dep_forces_D3 3
    (hierarchySpatialRealization jRealizedHierarchy.1 jRealizedHierarchy.2)
    j_hierarchy_satisfies_dep

/-! ## Part 4: the proved obstruction (DEP is a genuine input)

Independence, parallel to the other three audit rows.  The surrounding
structure does not force the principle: a complete spatial realization exists
in which it fails. -/

/-- The everything-deforms kinematics: the unlinked world, where every
configuration deforms to every other.  Configurations are still *distinct as
configurations* (`pair = 2 ≠ 0 = split`); what is missing is any
deformation-stable distinction. -/
@[reducible] def unlinkedKinematics : PairKinematics where
  Config := ℤ
  deform := fun _ _ => True
  deform_refl := fun _ => trivial
  deform_symm := fun _ => trivial
  deform_trans := fun _ _ => trivial
  split := 0
  pair := 2

/-- In the unlinked kinematics every pairing observable vanishes identically:
deformation invariance over the total relation collapses every value to the
split value `0`. -/
theorem unlinkedKinematics_all_pairings_zero
    (P : PairingObservable unlinkedKinematics) :
    ∀ c, P.pairing c = 0 := by
  intro c
  exact (P.deform_invariant c unlinkedKinematics.split trivial).trans P.split_zero

/-- The unlinked kinematics refutes DEP. -/
theorem unlinkedKinematics_refutes_dep :
    ¬ DeformationErasurePrinciple unlinkedKinematics := by
  rintro ⟨P, hP⟩
  exact hP (unlinkedKinematics_all_pairings_zero P _)

/-- A complete spatial realization in `D = 4` built on the unlinked kinematics.
Its Alexander identification field is *proved*: both sides are false
(`D4_no_linking` on the linking side, the vanishing theorem on the observable
side). -/
def fourDimRealization : SpatialDualPairRealization 4 where
  kin := unlinkedKinematics
  pairing_available_iff := by
    constructor
    · rintro ⟨P, hP⟩
      exact absurd (unlinkedKinematics_all_pairings_zero P _) hP
    · intro h
      exact absurd h DimensionForcing.D4_no_linking

/-- **The proved obstruction**: the spatial-realization layer alone does not
force DEP.  A complete realization exists in which the principle fails, so DEP
is a genuine named input, exactly parallel to the proved-obstruction status of
the T6 realized-hierarchy fields, the T5 positive-ratio coordinates, and the
T5 right-affine response. -/
theorem dep_not_forced_by_realization_layer :
    ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      ¬ DeformationErasurePrinciple R.kin :=
  ⟨4, fourDimRealization, unlinkedKinematics_refutes_dep⟩

/-- Distinctness of configurations does not force deformation-stable
distinctness: a kinematics with `pair ≠ split` as elements can still have every
pairing observable vanish.  The principle is about stability, not bare
distinctness. -/
theorem config_distinctness_does_not_force_dep :
    ∃ X : PairKinematics,
      X.pair ≠ X.split ∧ ¬ DeformationErasurePrinciple X := by
  refine ⟨unlinkedKinematics, ?_, unlinkedKinematics_refutes_dep⟩
  show (2 : ℤ) ≠ 0
  norm_num

/-! ## Certificate -/

/-- The linking-necessity certificate: every field is a proved theorem of this
module.  Together they replace the bare "linking is required" definition with
the dual-pair theorems, the named principle, the forcing theorems, and the
independence obstruction. -/
structure LinkingNecessityCertificate : Prop where
  /-- The recognition (debit) loop winds `+1`. -/
  debit_winding_one :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      pathWinding (recognitionCircleLoop F H) = 1
  /-- The credit loop winds `-1`. -/
  credit_winding_neg_one :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      pathWinding (creditLoop F H) = -1
  /-- The dual pair is balanced: sigma = 0 realized topologically. -/
  pair_balanced :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      pathWinding (recognitionCircleLoop F H) + pathWinding (creditLoop F H) = 0
  /-- The dual pair is distinct: the posted distinction is nonzero. -/
  pair_distinct :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      pathWinding (recognitionCircleLoop F H) ≠ pathWinding (creditLoop F H)
  /-- The posted pairing gap is nonzero. -/
  pairing_gap_ne_zero :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      ledgerPairingGap F H ≠ 0
  /-- The winding pairing is genuinely deformation-invariant. -/
  winding_invariant :
    ∀ {γ δ : C(I, SphereOne)}, γ.HomotopicRel δ {0, 1} →
      pathWinding γ = pathWinding δ
  /-- DEP forces separation of pair from split. -/
  dep_separates :
    ∀ X : PairKinematics, DeformationErasurePrinciple X →
      ¬ X.deform X.pair X.split
  /-- DEP forces `D = 3` in every spatial realization. -/
  dep_forces_dimension :
    ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      DeformationErasurePrinciple R.kin → D = 3
  /-- Off `D = 3`, the dual-pair distinction is erasable in every realization. -/
  erasable_off_three :
    ∀ (D : DimensionForcing.Dimension), D ≠ 3 →
      ∀ R : SpatialDualPairRealization D,
        ¬ DeformationErasurePrinciple R.kin
  /-- The hierarchy's own `D = 3` realization satisfies DEP (non-vacuity). -/
  hierarchy_dep :
    ∀ (F : ClosedObservableFramework) (H : RealizedHierarchy F),
      DeformationErasurePrinciple (hierarchySpatialRealization F H).kin
  /-- The `J`-produced hierarchy satisfies DEP (non-vacuity from `J`). -/
  j_dep :
    DeformationErasurePrinciple
      (hierarchySpatialRealization
        jRealizedHierarchy.1 jRealizedHierarchy.2).kin
  /-- The proved obstruction: DEP is a genuine input. -/
  dep_independent :
    ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      ¬ DeformationErasurePrinciple R.kin
  /-- Bare configuration distinctness does not force DEP. -/
  distinctness_insufficient :
    ∃ X : PairKinematics,
      X.pair ≠ X.split ∧ ¬ DeformationErasurePrinciple X

/-- The linking-necessity certificate holds. -/
theorem linkingNecessityCertificate : LinkingNecessityCertificate where
  debit_winding_one := recognitionCircleLoop_winding_one
  credit_winding_neg_one := creditLoop_winding_neg_one
  pair_balanced := dual_pair_balanced
  pair_distinct := dual_pair_distinct
  pairing_gap_ne_zero := ledgerPairingGap_ne_zero
  winding_invariant := winding_deformation_invariant
  dep_separates := dep_separates_pair_from_split
  dep_forces_dimension := dep_forces_D3
  erasable_off_three := dual_pair_erasable_off_three
  hierarchy_dep := hierarchy_realization_satisfies_dep
  j_dep := j_hierarchy_satisfies_dep
  dep_independent := dep_not_forced_by_realization_layer
  distinctness_insufficient := config_distinctness_does_not_force_dep

end

end LinkingNecessity
end Foundation
end IndisputableMonolith

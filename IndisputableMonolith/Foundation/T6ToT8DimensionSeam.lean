import Mathlib
import IndisputableMonolith.Foundation.T5ToT6HierarchySeam
import IndisputableMonolith.Foundation.DistinctionToPhi
import IndisputableMonolith.Foundation.DistinctionToDimension
import IndisputableMonolith.Foundation.LinkingNecessity
import IndisputableMonolith.Foundation.LinkingFromHierarchy
import IndisputableMonolith.Foundation.ChainObstructions
import IndisputableMonolith.Foundation.GoldenHierarchyFromJ

/-!
# T6 → T8 dimension seam: what named T6 supplies, what still must be named

Mission receipt after `T5ToT6HierarchySeam`.

Named T6 (φ closed scale / `T6_FromDistinction`) supplies hierarchy material
toward linking. It does **not** force the Deformation Erasure Principle (DEP)
on every spatial dual-pair realization: the D=4 unlinked decoy coexists with
T6 and refutes DEP.

The upgrade to `D = 3` is:

* **obstruction route:** bare T6 + spatial realization layer ↛ DEP;
* **named-premise route:** T6 supply + `LinkingNecessity` / hierarchy-linking
  premises (DEP on a spatial realization, or realized hierarchy → Mathlib
  circle linking) yield `SupportsNontrivialLinking 3` and hence `D = 3`.

T7 stays downstream: once `D = 3`, the period is `2^3 = 8`.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace T6ToT8DimensionSeam

open DistinctionToPhi
open DistinctionToDimension
open T5ToT6HierarchySeam
open LinkingNecessity
open LinkingFromHierarchy
open ClosedFramework
open HierarchyRealization

/-! ## 1. What named T6 supplies toward T8 -/

/-- Exact inventory of what the named T6 φ-hierarchy surface gives T8. -/
structure T6SupplyTowardT8 : Prop where
  /-- Named T5→T6 hierarchy seam (supply, COF decoy, hierarchy-from-`J`). -/
  t5_t6_seam : T5ToT6SeamCert
  /-- Distinction-threaded T6 for every object distinction. -/
  t6_from_distinction :
    ∀ {K : Type} (h : ∃ x y : K, x ≠ y), T6_FromDistinction h
  /-- Closed φ-scale model from named hierarchy-from-`J` premises. -/
  closed_phi_scale :
    ∃ (F : ClosedObservableFramework)
      (M : HierarchyRealizationFromScale.RealizedClosedScaleModel F),
      M.scales.ratio = Constants.phi
  /-- A concrete `J`-produced realized hierarchy exists (non-vacuity for
  hierarchy→linking). -/
  j_realized_hierarchy :
    ∃ (F : ClosedObservableFramework), Nonempty (RealizedHierarchy F)
  /-- Once linking is supported, dimension is forced to `3`. -/
  linking_forces_D3 :
    ∀ D : DimensionForcing.Dimension,
      DimensionForcing.SupportsNontrivialLinking D → D = 3

/-- The named T6 surface supplies exactly the inventory above. -/
theorem t6_supply_toward_T8 : T6SupplyTowardT8 where
  t5_t6_seam := t5ToT6SeamCert
  t6_from_distinction := fun h => distinction_forces_T6 h
  closed_phi_scale := t6_phi_from_named_t5
  j_realized_hierarchy :=
    ⟨jRealizedHierarchy.1, ⟨jRealizedHierarchy.2⟩⟩
  linking_forces_D3 := DimensionForcing.linking_requires_D3

/-! ## 2. Kernel obstruction: bare T6 does not force DEP / linking -/

/-- **Obstruction.** Even given distinction-threaded T6, the spatial dual-pair
realization layer admits a model (D=4 unlinked) that refutes DEP. So bare T6
does not manufacture deformation-stable linking. -/
theorem bare_t6_does_not_force_DEP
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (h6 : T6_FromDistinction h) :
    T6_FromDistinction h ∧
      ∃ (D : DimensionForcing.Dimension)
        (R : SpatialDualPairRealization D),
        ¬ DeformationErasurePrinciple R.kin :=
  ⟨h6, ChainObstructions.linking_interpretation_obstruction⟩

/-- Concrete decoy: D=4 unlinked kinematics refutes DEP while T6 remains. -/
theorem t6_coexists_with_unlinked_D4_decoy
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (h6 : T6_FromDistinction h) :
    T6_FromDistinction h ∧
      ¬ DeformationErasurePrinciple fourDimRealization.kin :=
  ⟨h6, unlinkedKinematics_refutes_dep⟩

/-- Config distinctness alone is not DEP (second decoy). -/
theorem omission_without_deformation_stability :
    ∃ X : PairKinematics,
      X.pair ≠ X.split ∧ ¬ DeformationErasurePrinciple X :=
  config_distinctness_does_not_force_dep

/-- Supply toward T8 coexists with the DEP independence obstruction. -/
theorem t6_supply_and_dep_obstruction :
    T6SupplyTowardT8 ∧
      ∃ (D : DimensionForcing.Dimension)
        (R : SpatialDualPairRealization D),
        ¬ DeformationErasurePrinciple R.kin :=
  ⟨t6_supply_toward_T8, ChainObstructions.linking_interpretation_obstruction⟩

/-! ## 3. Named dimension / linking premises -/

/-- Named T8 dimension premises: DEP / hierarchy→linking facts needed beyond
bare T6. Kept as concrete theorems (not the universe-polymorphic certificate
aggregators) so the seam stays universe-clean. -/
structure DimensionT8BridgePremises : Prop where
  /-- DEP on a spatial realization forces `D = 3`. -/
  dep_forces_dimension :
    ∀ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      DeformationErasurePrinciple R.kin → D = 3
  /-- Any realized hierarchy supports nontrivial linking in `D = 3`. -/
  hierarchy_forces_linking :
    ∀ (F : ClosedObservableFramework) (_H : RealizedHierarchy F),
      DimensionForcing.SupportsNontrivialLinking 3
  /-- Concrete `J`-hierarchy forces linking in `D = 3`. -/
  j_hierarchy_forces_linking : DimensionForcing.SupportsNontrivialLinking 3
  /-- DEP independence: spatial realization alone does not force DEP. -/
  dep_independent :
    ∃ (D : DimensionForcing.Dimension) (R : SpatialDualPairRealization D),
      ¬ DeformationErasurePrinciple R.kin

/-- The named dimension premises, discharged from existing theorems. -/
theorem dimensionT8BridgePremises : DimensionT8BridgePremises where
  dep_forces_dimension := dep_forces_D3
  hierarchy_forces_linking := hierarchy_forces_linking_D3
  j_hierarchy_forces_linking := jRealizedHierarchy_forces_linking_D3
  dep_independent := dep_not_forced_by_realization_layer

/-- **Upgrade.** Named T6 supply plus named dimension premises yield
`SupportsNontrivialLinking 3` (hence `D = 3` by the linking route). -/
theorem t8_linking_from_t6_supply_plus_dimension
    (_supply : T6SupplyTowardT8)
    (bridge : DimensionT8BridgePremises) :
    DimensionForcing.SupportsNontrivialLinking 3 ∧
      (∀ D : DimensionForcing.Dimension,
        DimensionForcing.SupportsNontrivialLinking D → D = 3) :=
  ⟨bridge.j_hierarchy_forces_linking, DimensionForcing.linking_requires_D3⟩

/-- Specialization with discharged packages. -/
theorem t8_D3_from_named_t6 :
    DimensionForcing.SupportsNontrivialLinking 3 ∧
      (∀ D : DimensionForcing.Dimension,
        DimensionForcing.SupportsNontrivialLinking D → D = 3) := by
  exact t8_linking_from_t6_supply_plus_dimension
    t6_supply_toward_T8 dimensionT8BridgePremises

/-- Attached form: T6 plus DEP on a spatial realization forces `D = 3`. -/
theorem t8_D3_from_t6_plus_DEP
    {K : Type} {h : ∃ x y : K, x ≠ y}
    (_h6 : T6_FromDistinction h)
    (D : DimensionForcing.Dimension)
    (R : SpatialDualPairRealization D)
    (hDEP : DeformationErasurePrinciple R.kin) :
    D = 3 :=
  dep_forces_D3 D R hDEP

/-- Distinction packaging factors as T6 + global linking/dimension theorems. -/
theorem distinction_forces_T8_factors
    {K : Type} (h : ∃ x y : K, x ≠ y) :
    T8_FromDistinction h :=
  distinction_forces_T8 h

/-- T7 remains downstream of T8. -/
theorem t7_downstream_of_forced_D3 :
    DimensionForcing.EightTickFromDimension 3 =
      DimensionForcing.eight_tick :=
  rfl

/-! ## 4. Certificate -/

/-- Machine-checkable T6 → T8 dimension seam certificate. -/
structure T6ToT8SeamCert : Prop where
  /-- What named T6 supplies toward T8. -/
  supply : T6SupplyTowardT8
  /-- Bare T6 coexists with DEP-refuting spatial realizations. -/
  bare_t6_obstruction :
    ∀ {K : Type} {h : ∃ x y : K, x ≠ y},
      T6_FromDistinction h →
        T6_FromDistinction h ∧
          ∃ (D : DimensionForcing.Dimension)
            (R : SpatialDualPairRealization D),
            ¬ DeformationErasurePrinciple R.kin
  /-- Concrete D=4 unlinked decoy. -/
  decoy_unlinked_D4 :
    ∀ {K : Type} {h : ∃ x y : K, x ≠ y},
      T6_FromDistinction h →
        T6_FromDistinction h ∧
          ¬ DeformationErasurePrinciple fourDimRealization.kin
  /-- Config distinctness omission decoy. -/
  decoy_distinctness_insufficient :
    ∃ X : PairKinematics,
      X.pair ≠ X.split ∧ ¬ DeformationErasurePrinciple X
  /-- Named dimension / linking premises. -/
  dimension_premises : DimensionT8BridgePremises
  /-- Upgrade: T6 supply + dimension premises ⊢ linking at D=3. -/
  upgrade :
    T6SupplyTowardT8 →
      DimensionT8BridgePremises →
        DimensionForcing.SupportsNontrivialLinking 3 ∧
          (∀ D : DimensionForcing.Dimension,
            DimensionForcing.SupportsNontrivialLinking D → D = 3)
  /-- Attached T6 + DEP forces D=3. -/
  attached_dep_forces_D3 :
    ∀ {K : Type} {h : ∃ x y : K, x ≠ y},
      T6_FromDistinction h →
        ∀ (D : DimensionForcing.Dimension)
          (R : SpatialDualPairRealization D),
          DeformationErasurePrinciple R.kin → D = 3
  /-- T7 stays downstream. -/
  t7_downstream :
    DimensionForcing.EightTickFromDimension 3 =
      DimensionForcing.eight_tick

/-- The T6 → T8 dimension seam certificate. -/
theorem t6ToT8SeamCert : T6ToT8SeamCert where
  supply := t6_supply_toward_T8
  bare_t6_obstruction := fun h6 => bare_t6_does_not_force_DEP h6
  decoy_unlinked_D4 := fun h6 => t6_coexists_with_unlinked_D4_decoy h6
  decoy_distinctness_insufficient := omission_without_deformation_stability
  dimension_premises := dimensionT8BridgePremises
  upgrade := fun supply bridge =>
    t8_linking_from_t6_supply_plus_dimension supply bridge
  attached_dep_forces_D3 := fun h6 D R hDEP =>
    t8_D3_from_t6_plus_DEP h6 D R hDEP
  t7_downstream := t7_downstream_of_forced_D3

end T6ToT8DimensionSeam
end Foundation
end IndisputableMonolith

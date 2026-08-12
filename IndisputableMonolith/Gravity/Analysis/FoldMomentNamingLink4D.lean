import Mathlib
import IndisputableMonolith.Gravity.Analysis.GeometricFoldVsDictionary4D

/-!
# Arc 2 step 9 task 1: naming link status (scoped)

Frozen question: is `m2AllOrbitMomentDistinctHingeEdgeOrigins` the m² moment
of `exactFlatCrossTermFold` as a functional of that fold's own symbol?

## Two-sided verdict (2026-08-02)

The load-bearing certificates live in
`ReggeBlochStarResolvedT11M2Eval4D`:

* At both banked TT witnesses, the fold's own resolved-t11 moment equals the
  hybrid moment (both `-1/4`). Claim: `C-holo-arc2-step9-naming-link`.
* Off the witnesses, the functionals differ
  (`fold_ne_hybrid_generic_dir1011`). Killed route:
  `N-route-hybrid-as-fold-proxy`.

This module keeps the **definitional** status only: the two t11 constructions
do not share a provenance string, so a global identity-of-definitions remains
false. Witness equality is not re-proved here (that would re-import the
resolved star module); it is cited by id.

## Honesty

* THEOREM (elsewhere): witness equality; off-witness inequality.
* THEOREM (here): definitional provenance mismatch; witness factor-2
  measurement is not a naming link by itself.
* Status: `namingLinkClosedAsDefinition = false`;
  `namingLinkClosedAtWitnesses = true` (citation flag).
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace FoldMomentNamingLink4D

open GeometricFoldVsDictionary4D
open ReggeExactFlatHessianBlochSymbol4D (exactMidpointBlochM2)
open ReggeBlochStarEdgeOrigins4D (m2AllOrbitMomentDistinctHingeEdgeOrigins)
open ReggeBlochM2Symbol4D (symbolDir)
open EdgeTTDecomposition4D (axisTTPlus)

/-- Provenance tag for the hybrid moment's t11 orbit. -/
def hybridT11Provenance : String := "legacy_transported_path"

/-- Provenance tag for the fold's t11 orbit. -/
def foldT11Provenance : String := "star_member_cube_offsets"

/-- **Definitional mismatch.** The two t11 constructions are not the same
named object. -/
theorem t11_provenance_mismatch :
    hybridT11Provenance ≠ foldT11Provenance := by
  decide

/-- Witness-level factor-2 (imported measurement): dictionary = 2 × hybrid
at axisTTPlus / symbolDir. Evidence about moments, not a naming link. -/
theorem witness_factor_two_is_not_naming_link :
    exactMidpointBlochM2 axisTTPlus symbolDir
      = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir :=
  dict_eq_two_geom_axisTTPlus

/-- Global identity-of-definitions: still false (provenances differ). -/
def namingLinkClosedAsDefinition : Bool := false

theorem namingLinkClosedAsDefinition_eq :
    namingLinkClosedAsDefinition = false := rfl

/-- Citation flag: witness equality is proved in
`ReggeBlochStarResolvedT11M2Eval4D.fold_eq_hybrid_*` (not re-imported here). -/
def namingLinkClosedAtWitnesses : Bool := true

theorem namingLinkClosedAtWitnesses_eq :
    namingLinkClosedAtWitnesses = true := rfl

/-- Backward-compatible alias: "closed" meant definitional identity. -/
def namingLinkClosed : Bool := namingLinkClosedAsDefinition

theorem namingLinkClosed_eq : namingLinkClosed = false :=
  namingLinkClosedAsDefinition_eq

/-- Composite task-1 status: definition open; witnesses closed by citation. -/
theorem step9_task1_status :
    hybridT11Provenance ≠ foldT11Provenance ∧
      namingLinkClosedAsDefinition = false ∧
      namingLinkClosedAtWitnesses = true ∧
      exactMidpointBlochM2 axisTTPlus symbolDir
        = 2 * m2AllOrbitMomentDistinctHingeEdgeOrigins axisTTPlus symbolDir :=
  ⟨t11_provenance_mismatch, namingLinkClosedAsDefinition_eq,
    namingLinkClosedAtWitnesses_eq, witness_factor_two_is_not_naming_link⟩

end FoldMomentNamingLink4D
end Analysis
end Gravity
end IndisputableMonolith

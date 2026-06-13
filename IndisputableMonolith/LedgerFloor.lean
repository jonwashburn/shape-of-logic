import IndisputableMonolith.Foundation.RecognitionLedgerFloor
import IndisputableMonolith.Foundation.LedgerFloorT0Bridge

/-!
# Ledger Floor — the Boolean shadow of the extensive recognition ledger

This public aggregator exposes the ledger-floor layer that the core-theory PDF
cites: the free additive recognition ledger `DefectLedger I = I →₀ ℕ`, its
recognition cost, and the identification of the T0 Boolean floor as the
two-state *shadow* (truncation) of that extensive ledger.

Every declaration below is proved in Lean with no `sorry` and no project-local
axiom. The forced-quotient layer it stands on (`DistinctionToT4`,
`TMinus1ForcedFromDistinction`, the `TMinus1ToT0` Boolean recognition cost) is
the public core slice of the corresponding `/reality` modules.

## Public citation targets

* `DefectLedger` — the free commutative monoid `I →₀ ℕ` of primitive
  distinctions; the extensive recognition ledger.
* `ledgerCost` / `ledgerCost_add` — weighted recognition cost; additivity is
  unconditional (no gerrymandered independence relation).
* `two_independent_same_defects` — multiplicity is represented: two independent
  copies of one defect cost `2 w i`, not `w i`.
* `observable_floor_iff_pos_weight` — the observable equivalence is the kernel
  of the cost; the floor is non-vacuous iff some distinction has positive weight.
* `ledger_floor_t0_bridge` — for any distinction witness and strictly positive
  weight, the T0 floor is the surjective cost-and-join shadow of the extensive
  ledger.
* `ledger_t0_identification_certificate` — the packaged Phase-2 identification:
  the T0 floor is a genuine quotient (shadow) of the extensive ledger.
-/

namespace IndisputableMonolith
namespace LedgerFloor

open Foundation

/-! ## The extensive recognition ledger -/

/-- The defect ledger: finitely supported multiplicities of primitive
distinctions, the free commutative monoid on `I`. -/
abbrev DefectLedger := @Foundation.RecognitionLedgerFloor.DefectLedger

/-- Weighted recognition cost of a ledger. -/
noncomputable abbrev ledgerCost := @Foundation.RecognitionLedgerFloor.ledgerCost

/-- Unconditional additivity of the ledger cost. -/
abbrev ledgerCost_add := @Foundation.RecognitionLedgerFloor.ledgerCost_add

/-- Multiplicity is represented: two independent copies of one defect cost
`2 w i`. -/
abbrev two_independent_same_defects :=
  @Foundation.RecognitionLedgerFloor.two_independent_same_defects

/-- The observable equivalence is the cost kernel; the floor is non-vacuous iff
some distinction has positive weight. -/
abbrev observable_floor_iff_pos_weight :=
  @Foundation.RecognitionLedgerFloor.observable_floor_iff_pos_weight

/-- The Boolean T0 floor is the unit-weight truncation of the ledger. -/
abbrev boolean_floor_is_truncation :=
  @Foundation.RecognitionLedgerFloor.boolean_floor_is_truncation

/-! ## The T0 floor is the Boolean shadow of the ledger -/

/-- The bundled identification: the truncation map is a surjective cost-and-join
homomorphism from the extensive ledger onto the distinction-generated T0 floor. -/
abbrev LedgerFloorT0Bridge := @Foundation.LedgerFloorT0.LedgerFloorT0Bridge

/-- The Phase-2 identification holds for every distinction witness and every
strictly positive weight. -/
abbrev ledger_floor_t0_bridge := @Foundation.LedgerFloorT0.ledger_floor_t0_bridge

/-- The shadow lift surjects onto the T0 floor: every floor state is the shadow
of some ledger. -/
abbrev ledgerToFloor_surjective :=
  @Foundation.LedgerFloorT0.ledgerToFloor_surjective

/-- On a single primitive distinction the floor cost is the Boolean recognition
cost of the truncated multiplicity. -/
abbrev rank1_cost_is_boolean_truncation :=
  @Foundation.LedgerFloorT0.rank1_cost_is_boolean_truncation

/-- The packaged Phase-2 certificate: the T0 floor is a genuine quotient
(shadow) of the extensive recognition ledger. -/
abbrev ledger_t0_identification_certificate :=
  Foundation.LedgerFloorT0.ledger_t0_identification_certificate

end LedgerFloor
end IndisputableMonolith

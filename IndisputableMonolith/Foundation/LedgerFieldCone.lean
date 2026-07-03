import IndisputableMonolith.Foundation.LedgerField

/-!
# LedgerFieldCone: hub content-emptiness and the field-level widening cone

Two field-level facts that build on `Foundation.LedgerField` (the multi-voxel ledger).

## Hub content-emptiness (Cap3 `c3_l03`)

The panel's honest restatement of the "time-travel" claim: the hub vantage is
ADDRESS-COMPLETE but CONTENT-EMPTY for a single carrier. Addressing is total (every
committed index of every voxel is readable), but the value AT the present write-head, the
open frontier, is unwritten. `hub_content_empty` proves exactly this: reading a voxel at
its own write-head index returns `none`. The hub supplies addressing; a field supplies
content. There is no committed value at the frontier to retrieve, so no information is
transported from the future.

## Field-level widening cone (Cap3 `c3_l04`)

`LedgerTime.cone_card_monotone` proves the single-carrier admissible cone never shrinks.
`fieldCone_card_monotone` lifts that to the field: summing admissible-continuation counts
over a finite voxel set, the field cone count is nondecreasing in horizon. The future cone
widens; it never contracts.

Status: THEOREM (axiom-clean). MODEL only in the identification of `V`/`E` with physical
voxels and recognition entries.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerFieldCone

open IndisputableMonolith.Foundation.LedgerTime
open IndisputableMonolith.Foundation.LedgerField
open scoped BigOperators

variable {V : Type*} {E : Type*}

/-- **Hub content-emptiness.** Reading a voxel at its own present write-head index returns
`none`: the frontier is unwritten. The hub is address-complete (every committed index is
readable) but content-empty at the present (no committed value to retrieve from the
future). -/
theorem hub_content_empty (F : LedgerField V E) (v : V) :
    (F v)[writeHeadAt F v]? = none := by
  unfold writeHeadAt writeHead
  exact List.getElem?_eq_none (le_refl _)

variable [DecidableEq V]

/-- One step of the field-level admissible cone at a fixed voxel set, using a per-voxel
successor relation `next`. The cone over the field is the union of the per-voxel cones. -/
def fieldConeCard (next : E → Finset E) [DecidableEq E] (S : V → Finset E) (vs : Finset V) : ℕ :=
  ∑ v ∈ vs, (S v).card

/-- **Field-level widening cone.** The total admissible-continuation count over a finite
voxel set is nondecreasing under one cone step at every voxel: the field future cone never
shrinks. -/
theorem fieldCone_card_monotone (next : E → Finset E) [DecidableEq E]
    (S : V → Finset E) (vs : Finset V) :
    fieldConeCard next S vs ≤ fieldConeCard next (fun v => coneStep next (S v)) vs := by
  unfold fieldConeCard
  apply Finset.sum_le_sum
  intro v _
  exact cone_card_monotone next (S v)

/-- **Field time certificate.** The hub is content-empty at the frontier (no future
retrieval), and the field future cone is nondecreasing (it widens, never contracts). -/
structure FieldTimeCert : Prop where
  content_empty : ∀ {V E : Type*} (F : LedgerField V E) (v : V),
                    (F v)[writeHeadAt F v]? = none
  cone_widens : ∀ {V E : Type*} [DecidableEq V] (next : E → Finset E) [DecidableEq E]
                  (S : V → Finset E) (vs : Finset V),
                    fieldConeCard next S vs ≤ fieldConeCard next (fun v => coneStep next (S v)) vs

theorem fieldTimeCert : FieldTimeCert where
  content_empty := fun F v => hub_content_empty F v
  cone_widens := by
    intro V E _ next _ S vs
    exact fieldCone_card_monotone next S vs

end LedgerFieldCone
end Foundation
end IndisputableMonolith

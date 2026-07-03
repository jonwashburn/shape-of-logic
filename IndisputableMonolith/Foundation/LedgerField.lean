import IndisputableMonolith.Foundation.LedgerTime

/-!
# LedgerField: the multi-voxel (field-level) append-only ledger

`Foundation.LedgerTime` formalizes the append-only structure of recognition time for a
SINGLE carrier (one `List E`). Time-addressing at field scale needs the multi-voxel
generalization: a recognition FIELD is an assignment of an independent append-only ledger
to each voxel of a spatial index `V`. This module builds that type and lifts the
single-voxel theorems to it.

The type. `LedgerField V E := V → List E`: each voxel `v : V` carries its own committed
history. A field commit `commitAt v e` appends `e` to voxel `v` only, leaving every other
voxel untouched (locality: a write at one voxel does not edit another).

What this proves (the multi-voxel keystone for Cap3).

* `commitAt_local` (THEOREM): a commit at voxel `v` does not change any other voxel `w ≠ v`.
  Locality / no spooky cross-voxel edits.
* `past_immutable_at` (THEOREM): committing at `v` cannot alter the committed past of `v`
  (truncating back to the old length returns the old ledger). The field past is immutable.
* `writeHeadAt_advances` (THEOREM): the per-voxel write-head advances by exactly one at the
  written voxel, per commit.
* `writeHeadAt_other` (THEOREM): and is unchanged at every other voxel.
* `past_addressable_at` (THEOREM): every committed past index at the written voxel reads the
  same value after a new commit (address-stable readout).

Status: THEOREM (axiom-clean). MODEL only in identifying `V` with physical voxels and `E`
with recognition entries (argued in the companion paper, not here). The hub
content-emptiness (`c3_l03`) and the field-level widening cone (`c3_l04`) build on this type.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerField

open IndisputableMonolith.Foundation.LedgerTime

variable {V : Type*} {E : Type*}

/-- A recognition field: an independent append-only ledger at each voxel. -/
def LedgerField (V E : Type*) : Type _ := V → List E

variable [DecidableEq V]

/-- Commit entry `e` to voxel `v` of the field, leaving all other voxels untouched. -/
def commitAt (F : LedgerField V E) (v : V) (e : E) : LedgerField V E :=
  Function.update F v (commit (F v) e)

/-- The per-voxel write-head (present index at voxel `v`). -/
def writeHeadAt (F : LedgerField V E) (v : V) : ℕ := writeHead (F v)

/-- **Locality.** A commit at voxel `v` leaves every other voxel `w ≠ v` exactly as it was. -/
theorem commitAt_local (F : LedgerField V E) (v : V) (e : E) (w : V) (hw : w ≠ v) :
    commitAt F v e w = F w := by
  unfold commitAt
  rw [Function.update_of_ne hw]

/-- The value of the field at the written voxel after a commit is the single-voxel commit. -/
theorem commitAt_self (F : LedgerField V E) (v : V) (e : E) :
    commitAt F v e v = commit (F v) e := by
  unfold commitAt
  rw [Function.update_self]

/-- **Field past immutability.** Committing at `v` cannot alter the committed past of `v`. -/
theorem past_immutable_at (F : LedgerField V E) (v : V) (e : E) :
    (commitAt F v e v).take (F v).length = F v := by
  rw [commitAt_self]
  exact past_immutable (F v) e

/-- **Write-head advance (written voxel).** The present index at `v` moves forward by one. -/
theorem writeHeadAt_advances (F : LedgerField V E) (v : V) (e : E) :
    writeHeadAt (commitAt F v e) v = writeHeadAt F v + 1 := by
  unfold writeHeadAt
  rw [commitAt_self]
  exact writeHead_advances (F v) e

/-- **Write-head unchanged (other voxels).** No other voxel's present index moves. -/
theorem writeHeadAt_other (F : LedgerField V E) (v : V) (e : E) (w : V) (hw : w ≠ v) :
    writeHeadAt (commitAt F v e) w = writeHeadAt F w := by
  unfold writeHeadAt
  rw [commitAt_local F v e w hw]

/-- **Field past addressability.** Every committed past index at the written voxel reads the
same value after a new commit: the field past is read-only and addressable. -/
theorem past_addressable_at (F : LedgerField V E) (v : V) (e : E) (i : ℕ)
    (hi : i < (F v).length) :
    (commitAt F v e v)[i]? = (F v)[i]? := by
  rw [commitAt_self]
  exact past_addressable (F v) e i hi

/-- **Multi-voxel ledger certificate.** The field type is append-only, local (commits do not
edit other voxels), with an immutable addressable past and a per-voxel write-head that
advances by one at the written voxel and nowhere else. -/
structure FieldLedgerCert : Prop where
  local_write : ∀ {V E : Type*} [DecidableEq V] (F : LedgerField V E) (v : V) (e : E) (w : V),
                  w ≠ v → commitAt F v e w = F w
  past_immutable : ∀ {V E : Type*} [DecidableEq V] (F : LedgerField V E) (v : V) (e : E),
                     (commitAt F v e v).take (F v).length = F v
  head_advances : ∀ {V E : Type*} [DecidableEq V] (F : LedgerField V E) (v : V) (e : E),
                    writeHeadAt (commitAt F v e) v = writeHeadAt F v + 1
  head_other : ∀ {V E : Type*} [DecidableEq V] (F : LedgerField V E) (v : V) (e : E) (w : V),
                 w ≠ v → writeHeadAt (commitAt F v e) w = writeHeadAt F w
  addressable : ∀ {V E : Type*} [DecidableEq V] (F : LedgerField V E) (v : V) (e : E) (i : ℕ),
                  i < (F v).length → (commitAt F v e v)[i]? = (F v)[i]?

theorem fieldLedgerCert : FieldLedgerCert where
  local_write := fun F v e w hw => commitAt_local F v e w hw
  past_immutable := fun F v e => past_immutable_at F v e
  head_advances := fun F v e => writeHeadAt_advances F v e
  head_other := fun F v e w hw => writeHeadAt_other F v e w hw
  addressable := fun F v e i hi => past_addressable_at F v e i hi

end LedgerField
end Foundation
end IndisputableMonolith

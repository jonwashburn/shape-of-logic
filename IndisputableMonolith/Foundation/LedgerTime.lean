import Mathlib

/-!
# LedgerTime: the append-only structure of recognition time

The bare recognition tick is invertible, hence time-symmetric. The lived asymmetry
between a fixed, readable past and an open, widening future is not in the tick; it
enters with the **ledger**: the append-only record of committed recognition events.

This module formalizes that structure abstractly over an entry type `E`:

* `commit` appends a new entry (append-only, never edits in place);
* the **committed past** is immutable and addressable under a new commit
  (`past_immutable`, `past_addressable`), and the write-head advances by exactly
  one (`writeHead_advances`);
* the **admissible future cone** never shrinks (`cone_grows`,
  `cone_card_monotone`): the count of admissible continuations is nondecreasing in
  horizon.

Status: THEOREM for the structural facts (these are standard list/finset lemmas).
MODEL for the identification of `E` with recognition entries and of `coneStep`
with the J-admissible continuation set; that identification is argued in the
companion paper, not here.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LedgerTime

variable {E : Type*}

/-- Commit a new entry to the ledger: append-only. -/
def commit (l : List E) (e : E) : List E := l ++ [e]

/-- The write-head index (the present): the number of committed entries. -/
def writeHead (l : List E) : ℕ := l.length

/-- **Past immutability.** Truncating the extended ledger back to the old length
returns the old ledger exactly: committing a new entry cannot alter the past.

Strategy: `unfold commit; exact List.take_left l [e]` (or
`simp [commit, List.take_left]`). -/
theorem past_immutable (l : List E) (e : E) :
    (commit l e).take l.length = l := by
  unfold commit; simp

/-- **Write-head advance.** The present index moves forward by exactly one per
commit.

Strategy: `simp [writeHead, commit, List.length_append]`. -/
theorem writeHead_advances (l : List E) (e : E) :
    writeHead (commit l e) = writeHead l + 1 := by
  unfold writeHead commit; simp

/-- **Past addressability.** Every committed past index reads the same value after
a new commit: the past is read-only and addressable by index.

Strategy: `unfold commit; exact List.getElem?_append_left hi` (find the exact
`getElem?_append` lemma for the index-in-left-segment case via the premises). -/
theorem past_addressable (l : List E) (e : E) (i : ℕ) (hi : i < l.length) :
    (commit l e)[i]? = l[i]? := by
  unfold commit; rw [List.getElem?_append_left hi]

variable [DecidableEq E]

/-- One step of the admissible future cone: the current frontier together with all
its admissible successors under `next`. -/
def coneStep (next : E → Finset E) (S : Finset E) : Finset E :=
  S ∪ S.biUnion next

/-- **The cone never shrinks.** The frontier is contained in its successor cone.

Strategy: `unfold coneStep; exact Finset.subset_union_left`. -/
theorem cone_grows (next : E → Finset E) (S : Finset E) :
    S ⊆ coneStep next S := by
  unfold coneStep; exact Finset.subset_union_left

/-- **Admissible count nondecreasing.** The number of admissible states is
nondecreasing in horizon.

Strategy: `exact Finset.card_le_card (cone_grows next S)`. -/
theorem cone_card_monotone (next : E → Finset E) (S : Finset E) :
    S.card ≤ (coneStep next S).card := by
  exact Finset.card_le_card (cone_grows next S)

end LedgerTime
end Foundation
end IndisputableMonolith

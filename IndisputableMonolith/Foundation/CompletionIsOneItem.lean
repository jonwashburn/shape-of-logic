import Mathlib
import IndisputableMonolith.Loom.LoopSpace
import IndisputableMonolith.Foundation.OctaveFloorStep
import IndisputableMonolith.Foundation.RequirementFromLedgerClosure

/-!
# Completion is one item of the floor above: why the pass is complete

The question (Ray, Simons, Thapa, 2026-09-01): the primitives `βᵢ : C → {0,1}`
explain why the recognizer's states form a cube, but nothing explains why a
recognizer should move through every one of those states. The eight-tick cadence
is proved as the minimum *given* that a completed recognition visits all eight
patterns, and every paper that uses the cadence carries "a completed recognition
is a full pass" as a premise.

This module replaces that premise with a definition that says what "completed"
means in the ledger, and proves that the full pass follows from it.

**Definition (completion).** A pass is *completed* when it is legible as one
unit at the next scale: the floor step (`OctaveFloorStep`) says a position of
the recognizer's lattice is a pattern together with an address, and the address
is the item of the floor above. A pass *occupies* an item when every position of
that item has its pattern visited by the pass (`OccupiesItem`). A completed
recognition is one that occupies an item.

**Theorems.**

* `occupiesItem_iff_complete`: a pass occupies an item if and only if it visits
  every pattern. The fiber of an item is one complete octave
  (`item_fiber_full_octave`), so occupying it *is* visiting all `2^d` states.
  The complete pass is not a premise about dynamics; it is what "one item at the
  next floor" means.
* `closed_complete_length`: a closed pass that visits every pattern has at least
  `2^d` steps. At `d = 3`, `eight_le_of_closed_complete`: at least eight.
* `grayWalk_closed`, `grayWalk_complete`, `grayWalk_length`: the bound is
  attained, by the Gray cycle, in exactly eight steps.
* `faceWalk_closed`, `faceWalk_not_complete`, `faceWalk_not_item`: the decoy. A
  single face of the cube, run once, is closed and balances every account, and
  it is not an item of the floor above. Closure alone does not complete a
  recognition; only a pass that the floor above can read as one unit does.

**What this settles and what it does not.** It settles what a completed
recognition is and why it visits every state: completion means posting one
item upward, and the fiber of an item is the whole octave. It does not say why
a recognizer moves at all; that is the process postulate (recognition proceeds
by acts, one per tick), and no theorem here touches it. And the identification
of "completed" with "legible one floor up" is a definition. It is the ledger's
own meaning of a completed posting, a record that a coarser reader can take as
one entry, and it is stated as such.

Tier: `OccupiesItem` as the definition of completion is MODEL. Every theorem
under it is THEOREM (kernel-checked, base triple).
-/

namespace IndisputableMonolith
namespace Foundation
namespace CompletionIsOneItem

open IndisputableMonolith.Patterns
open IndisputableMonolith.Foundation.OctaveFloorStep
open IndisputableMonolith.Foundation.RequirementFromLedgerClosure

variable {d : ℕ}

/-! ## What a pass visits -/

/-- The states a history visits, start and end included. -/
def visited (p : Pattern d) : List (Fin d) → List (Pattern d)
  | [] => [p]
  | a :: L => p :: visited (Loom.flip p a) L

/-- The states a history stands on before each of its acts: one per act. -/
def visitedBefore (p : Pattern d) : List (Fin d) → List (Pattern d)
  | [] => []
  | a :: L => p :: visitedBefore (Loom.flip p a) L

theorem visitedBefore_length (p : Pattern d) (L : List (Fin d)) :
    (visitedBefore p L).length = L.length := by
  induction L generalizing p with
  | nil => rfl
  | cons a L ih => simp [visitedBefore, ih]

theorem mem_visited (p : Pattern d) (L : List (Fin d)) (q : Pattern d)
    (h : q ∈ visited p L) :
    q ∈ visitedBefore p L ∨ q = List.foldl Loom.flip p L := by
  induction L generalizing p with
  | nil =>
    right
    simpa [visited] using h
  | cons a L ih =>
    simp only [visited, List.mem_cons] at h
    rcases h with rfl | h
    · left
      simp [visitedBefore]
    · rcases ih (Loom.flip p a) h with h' | h'
      · left
        simp [visitedBefore, h']
      · right
        simpa [List.foldl_cons] using h'

/-- A complete pass: every pattern is visited. -/
def Complete (w : Loom.Walk d) : Prop :=
  ∀ q : Pattern d, q ∈ visited w.start w.steps

instance (w : Loom.Walk d) : Decidable (Complete w) := by
  unfold Complete
  infer_instance

/-! ## Completion: the pass occupies one item of the floor above -/

/-- The pass occupies the item `a` of the floor above: every position whose
address is `a` has its pattern visited. This is the definition of a completed
recognition: one the floor above can read as a single unit. -/
def OccupiesItem (w : Loom.Walk d) (a : Fin d → ℤ) : Prop :=
  ∀ x : Fin d → ℤ, addressD x = a → (parityD x : Pattern d) ∈ visited w.start w.steps

/-- **Occupying an item is visiting every pattern.** The fiber of one item is one
complete octave, so a pass is legible as one unit at the floor above exactly when
it is complete. -/
theorem occupiesItem_iff_complete (w : Loom.Walk d) (a : Fin d → ℤ) :
    OccupiesItem w a ↔ Complete w := by
  constructor
  · intro h q
    have hx := h (assembleD q a) (addressD_assembleD q a)
    rwa [parityD_assembleD] at hx
  · intro h x _
    exact h _

/-- Completeness does not depend on which item: a complete pass occupies every
item, an incomplete one occupies none. -/
theorem occupiesItem_iff_occupiesItem (w : Loom.Walk d) (a b : Fin d → ℤ) :
    OccupiesItem w a ↔ OccupiesItem w b := by
  rw [occupiesItem_iff_complete, occupiesItem_iff_complete]

/-! ## A closed complete pass has at least `2^d` acts -/

theorem card_le_length_of_forall_mem {α : Type*} [Fintype α] [DecidableEq α]
    (L : List α) (h : ∀ q, q ∈ L) : Fintype.card α ≤ L.length :=
  calc Fintype.card α = Finset.univ.card := Finset.card_univ.symm
    _ ≤ L.toFinset.card :=
        Finset.card_le_card (fun q _ => List.mem_toFinset.2 (h q))
    _ ≤ L.length := List.toFinset_card_le L

/-- **The cadence bound.** A closed pass that visits every pattern has at least
`2^d` acts: it stands on a distinct state before each of `2^d` acts. -/
theorem closed_complete_length (hd : 0 < d) (w : Loom.Walk d)
    (hc : w.Closed) (hcomp : Complete w) : 2 ^ d ≤ w.steps.length := by
  have hcard : Fintype.card (Pattern d) = 2 ^ d := card_pattern d
  have hend : List.foldl Loom.flip w.start w.steps = w.start := hc
  rcases hL : w.steps with _ | ⟨a, L⟩
  · exfalso
    have h1 : Fintype.card (Pattern d) ≤ 1 := by
      have := card_le_length_of_forall_mem (visited w.start w.steps) hcomp
      rw [hL] at this
      simpa [visited] using this
    have h2 : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega
  · rw [← visitedBefore_length w.start (a :: L), ← hcard]
    apply card_le_length_of_forall_mem
    intro q
    rcases mem_visited w.start w.steps q (hcomp q) with h | h
    · rwa [hL] at h
    · rw [hend] at h
      subst h
      simp [visitedBefore]

/-- At `d = 3`: a closed complete pass has at least eight acts. -/
theorem eight_le_of_closed_complete (w : Loom.Walk 3) (hc : w.Closed) (hcomp : Complete w) :
    8 ≤ w.steps.length :=
  closed_complete_length (by norm_num) w hc hcomp

/-- Through the definition: a closed pass that occupies an item has at least
eight acts. -/
theorem eight_le_of_closed_item (w : Loom.Walk 3) (hc : w.Closed) (a : Fin 3 → ℤ)
    (h : OccupiesItem w a) : 8 ≤ w.steps.length :=
  eight_le_of_closed_complete w hc ((occupiesItem_iff_complete w a).1 h)

/-! ## The bound is attained: the Gray cycle -/

/-- The reflected Gray cycle on `Q_3`, as a history of eight acts. -/
def grayWalk : Loom.Walk 3 := ⟨fun _ => false, [0, 1, 0, 2, 0, 1, 0, 2]⟩

theorem grayWalk_closed : grayWalk.Closed := by decide

theorem grayWalk_complete : Complete grayWalk := by decide

theorem grayWalk_length : grayWalk.steps.length = 8 := rfl

/-- The Gray cycle occupies every item of the floor above. -/
theorem grayWalk_occupies (a : Fin 3 → ℤ) : OccupiesItem grayWalk a :=
  (occupiesItem_iff_complete grayWalk a).2 grayWalk_complete

/-! ## The decoy: a closed face is not an item -/

/-- One face of the cube, run once: four acts, closed. -/
def faceWalk : Loom.Walk 3 := ⟨fun _ => false, [0, 1, 0, 1]⟩

theorem faceWalk_closed : faceWalk.Closed := by decide

/-- The face balances every account: double entry is satisfied. -/
theorem faceWalk_balanced : ∀ i, (record faceWalk i).1 = (record faceWalk i).2 :=
  balanced_of_closed faceWalk faceWalk_closed

theorem faceWalk_not_complete : ¬ Complete faceWalk := by decide

/-- **Closure does not complete a recognition.** The face is closed and balanced
and occupies no item of the floor above. -/
theorem faceWalk_not_item (a : Fin 3 → ℤ) : ¬ OccupiesItem faceWalk a :=
  fun h => faceWalk_not_complete ((occupiesItem_iff_complete faceWalk a).1 h)

/-! ## Certificate -/

/-- Completion is one item: occupying an item is visiting every pattern; a closed
complete pass has at least `2^d` acts, eight at `d = 3`, attained by the Gray
cycle; a closed balanced face is not an item. -/
structure Cert : Prop where
  item_is_complete :
    ∀ {d : ℕ} (w : Loom.Walk d) (a : Fin d → ℤ), OccupiesItem w a ↔ Complete w
  cadence_bound :
    ∀ {d : ℕ}, 0 < d → ∀ (w : Loom.Walk d), w.Closed → Complete w → 2 ^ d ≤ w.steps.length
  eight_at_three :
    ∀ (w : Loom.Walk 3), w.Closed → ∀ a, OccupiesItem w a → 8 ≤ w.steps.length
  eight_attained :
    grayWalk.Closed ∧ Complete grayWalk ∧ grayWalk.steps.length = 8
  closed_face_is_not_an_item :
    faceWalk.Closed ∧ (∀ i, (record faceWalk i).1 = (record faceWalk i).2) ∧
      ∀ a, ¬ OccupiesItem faceWalk a

/-- The certificate holds. -/
theorem cert : Cert where
  item_is_complete := fun w a => occupiesItem_iff_complete w a
  cadence_bound := fun hd w hc hcomp => closed_complete_length hd w hc hcomp
  eight_at_three := fun w hc a h => eight_le_of_closed_item w hc a h
  eight_attained := ⟨grayWalk_closed, grayWalk_complete, grayWalk_length⟩
  closed_face_is_not_an_item := ⟨faceWalk_closed, faceWalk_balanced, faceWalk_not_item⟩

end CompletionIsOneItem
end Foundation
end IndisputableMonolith

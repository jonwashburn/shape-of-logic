import Mathlib
import IndisputableMonolith.Patterns.GrayCycle
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow5Tower

/-!
# Cutset row 5, the two traces named: reading an item is threading its pass

## The missing object

Arc 12 left row 5 at one sentence, "the ledger's pairing of the two traces is
their placement pairing", and found that the kernel could not reach it because
the two traces had never been named as objects of the tower. This module names
them.

A completed recognition at floor `F` is a full pass through the `2^D` corners of
one item: the Gray cycle (`Patterns.grayCycle3Path` at `D = 3`). Its record is
that item, one state of floor `F+1` (`CutsetRowA1Floor`). The floor above reads
items by its own pass, a Gray cycle through `2^D` items under the same rule (one
rule at every floor). So the two traces are the pass below, inside item `a`, and
the pass above, which visits `a` as one of its corners (`TwoTraces`). The record
is read when the pass above goes through `a`.

## What is computable, and is proved here

Three facts about the Gray cycle, each decided by the kernel:

* the cycle flips one axis on every other step, the *belt axis* (axis `0`), and
  every corner has exactly one belt-axis edge (`flipAxis_spec`, `belt_even`,
  `one_belt_edge`);
* projected along the belt axis the cycle goes once around the square of the
  other two axes, visiting its four corners in cyclic order, two steps at each
  (`belt_winds_once`): the pass is a belt around axis `0` inside its cube;
* the pass above, under the same rule, has at every item exactly one segment
  along the belt axis (`through_along_belt`): where it goes through item `a`, it
  runs along the axis the belt of `a` winds around.

## The topological reading (documented, not formalized here)

A segment along the belt axis through the centre of the cube crosses the surface
the belt spans exactly once, so in three dimensions the pass above threads the
belt of every item it reads with linking number one. In four dimensions two loops
never link: the pass above goes through the item (coverage forces that in every
dimension, `Patterns.GrayCycleGeneral`) and threads nothing. This step is
classical topology of the same class the tree already carries as a documented
identification (Alexander duality, `DimensionForcing`); this module adds no new
one and states the combinatorics the reading rests on.

## The word, restated

"Space keeps the record" becomes: *reading an item is threading its pass*. In
three dimensions the floor above's passing through the item is a linking, which
no motion inside the item (recognition-free for the floor above) can undo. In
four dimensions the passing is an address fact only, and an inside-item motion
can move the belt off the through-path: the reading is not a placement fact.
That is the cells-only world with a name in the tower: it is the tower in any
dimension but three. What remains for row 5 is whether "the floor above reads
the item" is the address fact or the threading fact; the plan for that is
`plans/Kernel_Cutset_Arc13_Plan_Reading_Is_Threading_20260903.html`.

## The sign, and where the tree already has it

The Gray cycle and its reverse complete the same item and are different runs
(`grayRev_surjective`, `grayRev_ne`); the address cannot tell them apart and the
circulation can (`circulation_gray = 4`, `circulation_grayRev = -4`, the bounce
`0`). This is the object `RequirementFromLedgerClosure` calls persistence
(`PersistedPostedDistinction`: the completed act stays distinguishable from its
reversal by something the substrate can post) and `RegistrationIsCochain`
classifies (a sign-of-the-run account is a holonomy account, `memoryBit` with
balance `4` on the square; the poster's own totals are blind,
`poster_record_blind`). What this module adds to those is the witness inside the
tower: in three dimensions the pass above is the account that reads the sign,
by the sign of its crossing. The residue is unchanged and is stated there:
persistence is a genuine input (`persistence_not_forced`, the `D = 4`
everything-deforms kinematics refutes it), grounded in MP informally, and the
carrier premise (one substrate, every account on a region of it) is what the
dimension argument still assumes beyond locality.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row5Threading

open Patterns

/-! ## The axis flipped at each step of the Gray cycle -/

/-- The axis flipped between step `i` and step `i + 1` of the Gray cycle:
axis `0` on even steps, axes `1` and `2` alternating on odd steps. -/
def flipAxis (i : Fin 8) : Fin 3 :=
  if i.val % 2 = 0 then 0 else if i.val % 4 = 1 then 1 else 2

/-- `flipAxis` is the axis at which consecutive Gray states differ, and the only
one. -/
theorem flipAxis_spec : ∀ (i : Fin 8) (j : Fin 3),
    grayCycle3Path i j ≠ grayCycle3Path (i + 1) j ↔ j = flipAxis i := by
  decide

/-- **The belt axis.** Axis `0` is flipped on exactly the even steps. -/
def beltAxis : Fin 3 := 0

theorem belt_even : ∀ i : Fin 8, flipAxis i = beltAxis ↔ i.val % 2 = 0 := by
  decide

/-- **Every corner has exactly one belt-axis edge.** The two edges at the corner
reached at step `i` are the steps `i - 1` and `i`; exactly one flips the belt
axis. -/
theorem one_belt_edge : ∀ i : Fin 8,
    (flipAxis (i - 1) = beltAxis ∧ flipAxis i ≠ beltAxis) ∨
    (flipAxis (i - 1) ≠ beltAxis ∧ flipAxis i = beltAxis) := by
  decide

/-! ## Projected along the belt axis, the pass winds once -/

/-- The projection of a state along the belt axis: its two other bits. -/
def proj (p : Pattern 3) : Bool × Bool := (p 1, p 2)

/-- The four corners of the square of axes `1, 2`, in cyclic order. -/
def square : Fin 4 → Bool × Bool :=
  ![(false, false), (true, false), (true, true), (false, true)]

/-- **The pass is a belt.** Projected along the belt axis, the Gray cycle visits
the square's four corners in cyclic order, two steps at each: it goes around
once. -/
theorem belt_winds_once : ∀ i : Fin 8,
    proj (grayCycle3Path i) = square ⟨i.val / 2, by omega⟩ := by
  decide

/-! ## The two traces -/

/-- **The two traces of a completed recognition in the tower.** The pass below
runs through the corners of item `a` at floor `F`; the pass above runs through
the items of floor `F + 1`, `a` among them, under the same rule. Both are the
Gray cycle: one rule at every floor. -/
structure TwoTraces where
  /-- The item at floor `F + 1` that the pass below completes. -/
  item : Fin 3 → ℤ
  /-- The pass below, on the corners of `item` (as residues). -/
  below : Fin 8 → Pattern 3
  /-- The pass above, on the items of floor `F + 1` (as residues of floor `F + 2`). -/
  above : Fin 8 → Pattern 3
  /-- One rule at every floor. -/
  below_rule : below = grayCycle3Path
  above_rule : above = grayCycle3Path
  /-- The pass above visits the item. -/
  visits : ∃ t : Fin 8, above t = fun j => decide (item j % 2 = 1)

/-- The canonical two traces in three dimensions, at the item `0`. -/
def canonical : TwoTraces where
  item := 0
  below := grayCycle3Path
  above := grayCycle3Path
  below_rule := rfl
  above_rule := rfl
  visits := ⟨0, by funext j; fin_cases j <;> rfl⟩

/-- **Where the pass above goes through an item, one of its two segments there
runs along the belt axis of the pass below.** -/
theorem through_along_belt (X : TwoTraces) (t : Fin 8) :
    (∀ j, X.above (t - 1) j ≠ X.above t j ↔ j = flipAxis (t - 1)) ∧
    (∀ j, X.above t j ≠ X.above (t + 1) j ↔ j = flipAxis t) ∧
    (flipAxis (t - 1) = beltAxis ∨ flipAxis t = beltAxis) := by
  rw [X.above_rule]
  refine ⟨?_, flipAxis_spec t, ?_⟩
  · have h := flipAxis_spec (t - 1)
    simpa [sub_add_cancel] using h
  · rcases one_belt_edge t with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h

/-- The pass below is the belt: same rule, same winding. -/
theorem below_is_belt (X : TwoTraces) (i : Fin 8) :
    proj (X.below i) = square ⟨i.val / 2, by omega⟩ := by
  rw [X.below_rule]; exact belt_winds_once i

/-! ## The sign: the reverse pass, the address, the circulation -/

/-- The Gray cycle run backwards: the same corners, the opposite orientation. -/
def grayRev : Fin 8 → Pattern 3 := fun i => grayCycle3Path (-i)

/-- The bounce: one bit up, one bit down, never completing. -/
def bounce : Fin 8 → Pattern 3 :=
  fun i => if i.val % 2 = 0 then (fun _ => false) else (fun j => decide (j.val = 0))

/-- G1a. The reverse run completes the same item: it is onto the octave. -/
theorem grayRev_surjective : Function.Surjective grayRev := by
  intro p
  obtain ⟨i, hi⟩ := grayCycle3_surjective p
  exact ⟨-i, by simpa [grayRev] using hi⟩

/-- G1b. The reverse run is a different run: the two histories part at step `1`. -/
theorem grayRev_ne : grayRev ≠ grayCycle3Path := by
  intro h
  have := congrFun (congrFun h 1) 2
  revert this
  decide

/-- G2. **The address is sign-blind.** Both runs occupy one item: every state of
either run has the same address (the item `0` here, since residues are patterns).
Read through `PassOccupiesItem`: both are onto, so both occupy the item. -/
theorem address_sign_blind :
    Function.Surjective grayCycle3Path ∧ Function.Surjective grayRev :=
  ⟨grayCycle3_surjective, grayRev_surjective⟩

/-- The next corner of the square in cyclic order. -/
def next : Bool × Bool → Bool × Bool
  | (false, false) => (true, false)
  | (true, false) => (true, true)
  | (true, true) => (false, true)
  | (false, true) => (false, false)

/-- The signed quarter-turn between two projected states: `+1` forward, `-1`
backward, `0` if unmoved (or diagonal, which a one-bit step never is). -/
def turn (a b : Bool × Bool) : ℤ :=
  if b = next a then 1 else if a = next b then -1 else 0

/-- **The circulation of a closed run**, in quarter turns around the belt axis. -/
def circulation (r : Fin 8 → Pattern 3) : ℤ :=
  turn (proj (r 0)) (proj (r 1)) + turn (proj (r 1)) (proj (r 2)) +
  turn (proj (r 2)) (proj (r 3)) + turn (proj (r 3)) (proj (r 4)) +
  turn (proj (r 4)) (proj (r 5)) + turn (proj (r 5)) (proj (r 6)) +
  turn (proj (r 6)) (proj (r 7)) + turn (proj (r 7)) (proj (r 0))

/-- G3. **The circulation reads the sign the address cannot.** The Gray cycle
goes once around (`+4` quarter turns), its reverse once around the other way
(`-4`), and the bounce, which completes nothing, has none. -/
theorem circulation_gray : circulation grayCycle3Path = 4 := by decide
theorem circulation_grayRev : circulation grayRev = -4 := by decide
theorem circulation_bounce : circulation bounce = 0 := by decide

/-! ## Certificate -/

structure Cert : Prop where
  /-- The flipped axis at each step, and only it. -/
  flip_spec : ∀ (i : Fin 8) (j : Fin 3),
    grayCycle3Path i j ≠ grayCycle3Path (i + 1) j ↔ j = flipAxis i
  /-- The belt axis is flipped on exactly the even steps. -/
  belt_even : ∀ i : Fin 8, flipAxis i = beltAxis ↔ i.val % 2 = 0
  /-- Every corner has exactly one belt-axis edge. -/
  one_belt_edge : ∀ i : Fin 8,
    (flipAxis (i - 1) = beltAxis ∧ flipAxis i ≠ beltAxis) ∨
    (flipAxis (i - 1) ≠ beltAxis ∧ flipAxis i = beltAxis)
  /-- Projected along the belt axis the pass winds once. -/
  winds_once : ∀ i : Fin 8, proj (grayCycle3Path i) = square ⟨i.val / 2, by omega⟩
  /-- The two traces exist in three dimensions. -/
  traces_exist : Nonempty TwoTraces
  /-- The pass above runs along the belt axis at every item it reads. -/
  through_belt : ∀ (X : TwoTraces) (t : Fin 8),
    flipAxis (t - 1) = beltAxis ∨ flipAxis t = beltAxis
  /-- The reverse run completes the same item and is a different run. -/
  reverse_same_item_other_run : Function.Surjective grayRev ∧ grayRev ≠ grayCycle3Path
  /-- The circulation carries the sign: `+4`, `-4`, and `0` for the bounce. -/
  circulation_signs : circulation grayCycle3Path = 4 ∧ circulation grayRev = -4 ∧
    circulation bounce = 0

theorem cert : Cert where
  flip_spec := flipAxis_spec
  belt_even := belt_even
  one_belt_edge := one_belt_edge
  winds_once := belt_winds_once
  traces_exist := ⟨canonical⟩
  through_belt := fun X t => (through_along_belt X t).2.2
  reverse_same_item_other_run := ⟨grayRev_surjective, grayRev_ne⟩
  circulation_signs := ⟨circulation_gray, circulation_grayRev, circulation_bounce⟩

end Row5Threading
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith

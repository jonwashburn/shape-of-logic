import Mathlib
import IndisputableMonolith.Foundation.CompletionIsOneItem
import IndisputableMonolith.Foundation.KernelClosure.FloorAndClock

/-!
# The clock row, closed by definition: one post per tick, one item upward

`FloorAndClock` left the clock row OPEN with expected closure. The terminal
class `SemanticClockLaw` was inhabited only by predicates that name their
coverage outright (`GrayCoverSemanticModel` asks for surjection; the measure
member asks for period `2^d` and a bijection), and the residual was a member
whose coverage is *derived* from what the ledger means, not written into the
predicate. The killed route `N-route-partiresiduals-appearance-bit-balanced-
surjection` fixed the bar: a non-packaging, recognition-native predicate that
forces `Pattern d` surjection and rejects the period-2 bounce.

`CompletionIsOneItem` (2026-09-01) supplies exactly that predicate. A completed
recognition is one the floor above can read as a single unit: the pass
*occupies an item* when every position of the recognizer's lattice sharing that
item has its pattern visited. Coverage is then a theorem about the floor step
(`item_fiber_full_octave`): the fiber of one item is one whole octave, so
occupying an item is visiting every pattern.

This module states that predicate on passes `Fin T → Pattern d`, pairs it with
the process postulate (recognition proceeds by one post per tick, so consecutive
states differ in one bit), and proves the pair is a member of `SemanticClockLaw`.

* `PassOccupiesItem pass a`: every position with address `a` has its pattern
  reached by some tick of the pass.
* `passOccupiesItem_iff_surjective`: occupying an item is surjection onto the
  cube. Coverage is derived, not assumed, and does not depend on which item.
* `CompletionClock pass`: one post per tick and the pass occupies an item.
* `completionClock_iff_grayCover`: extensionally this is the Gray-cover
  predicate, so the two earlier members were describing this one.
* `completionClockLaw : SemanticClockLaw`: the member. Gray-8 is complete; the
  six-post reciprocal pass and the period-2 bounce occupy no item; the jump
  cover posts two bits in one tick.
* `facePass`: the decoy of `CompletionIsOneItem` on passes. One face of the
  cube, run once, is one post per tick and closed, and occupies no item.

## Verdict

The clock row moves from OPEN to MODEL: the identification of "completed" with
"legible as one item of the floor above" is a definition, stated as such in
`CompletionIsOneItem`, and the one-post-per-tick clause is the process
postulate. Under those two named readings the complete pass, its eight-tick
minimum, and the Gray cycle as its attaining witness are theorems. What this
does not settle is why a recognizer moves at all; that is the process postulate
itself and no theorem here touches it. The numeral in the process clause is
removed in `CutsetRow6Tick`: the ledger's clock is the finest recognizer of
change, and the finest change is one bit by least count.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace ClockFromCompletion

open Patterns
open PublicSpine
open PublicSpine.PartINamedAxiomClosure
open PublicSpine.ClockDischargeProbe
open PublicSpine.PostingPhase3Wall
open OctaveFloorStep

/-! ## Completion on passes: occupying one item of the floor above -/

/-- The pass occupies the item `a` of the floor above: every position of the
recognizer's lattice whose address is `a` has its pattern reached at some tick.
This is what "completed" means in the ledger: legible as one unit one floor up. -/
def PassOccupiesItem {d T : ℕ} (pass : Fin T → Pattern d) (a : Fin d → ℤ) : Prop :=
  ∀ x : Fin d → ℤ, addressD x = a → ∃ t : Fin T, pass t = parityD x

/-- **Coverage is derived.** Occupying an item is reaching every pattern: the
fiber of one item is one complete octave. -/
theorem passOccupiesItem_iff_surjective {d T : ℕ}
    (pass : Fin T → Pattern d) (a : Fin d → ℤ) :
    PassOccupiesItem pass a ↔ Function.Surjective pass := by
  constructor
  · intro h q
    obtain ⟨t, ht⟩ := h (assembleD q a) (addressD_assembleD q a)
    exact ⟨t, by rw [ht, parityD_assembleD]⟩
  · intro h x _
    exact h _

/-- Which item is immaterial: a pass occupies every item or none. -/
theorem passOccupiesItem_iff_passOccupiesItem {d T : ℕ}
    (pass : Fin T → Pattern d) (a b : Fin d → ℤ) :
    PassOccupiesItem pass a ↔ PassOccupiesItem pass b := by
  rw [passOccupiesItem_iff_surjective, passOccupiesItem_iff_surjective]

/-! ## The process postulate on passes: one post per tick -/

/-- One post per tick: consecutive states differ in exactly one bit, the last
returning to the first. -/
def OnePostPerTick {d T : ℕ} [NeZero T] (pass : Fin T → Pattern d) : Prop :=
  ∀ i : Fin T, OneBitDiff (pass i) (pass (i + 1))

/-! ## The completion clock -/

/-- **The completion clock.** Recognition proceeds by one post per tick, and the
pass is completed: it occupies an item of the floor above. -/
def CompletionClock {d T : ℕ} (pass : Fin T → Pattern d) : Prop :=
  ∃ hT : NeZero T, @OnePostPerTick d T hT pass ∧ ∃ a : Fin d → ℤ, PassOccupiesItem pass a

/-- The completion clock is extensionally the Gray-cover predicate: the earlier
members of the class were naming the coverage this one derives. -/
theorem completionClock_iff_grayCover {d T : ℕ} (pass : Fin T → Pattern d) :
    CompletionClock pass ↔ GrayCoverSemanticModel pass := by
  constructor
  · rintro ⟨hT, hstep, a, hocc⟩
    exact ⟨hT, (passOccupiesItem_iff_surjective pass a).1 hocc, hstep⟩
  · rintro ⟨hT, hsurj, hstep⟩
    exact ⟨hT, hstep, fun _ => 0, (passOccupiesItem_iff_surjective pass _).2 hsurj⟩

theorem completionClock_gray8 : CompletionClock grayCycle3Path :=
  (completionClock_iff_grayCover grayCycle3Path).2 grayCoverSemanticModel_gray8

theorem completionClock_forces_surjective {d T : ℕ}
    (pass : Fin T → Pattern d) (h : CompletionClock pass) :
    Function.Surjective pass :=
  grayCoverSemanticModel_forces_surjective pass ((completionClock_iff_grayCover pass).1 h)

/-- The six-post reciprocal pass occupies no item. -/
theorem completionClock_rejects_six : ¬ CompletionClock balancedSixPostingPass :=
  fun h => grayCoverSemanticModel_rejects_six ((completionClock_iff_grayCover _).1 h)

/-- The jump cover reaches every pattern but posts two bits in one tick. -/
theorem completionClock_rejects_jump : ¬ CompletionClock jumpCover :=
  fun h => grayCoverSemanticModel_rejects_jump ((completionClock_iff_grayCover _).1 h)

/-- The period-2 bounce is one post per tick and occupies no item. -/
theorem completionClock_rejects_bounce : ¬ CompletionClock bouncePass :=
  fun h => bouncePass_not_surjective (completionClock_forces_surjective bouncePass h)

/-- **The member.** The completion clock inhabits the semantic clock law. -/
def completionClockLaw : SemanticClockLaw where
  completePass := fun {_ _} pass => CompletionClock pass
  gray8_complete := completionClock_gray8
  forces_surjective := completionClock_forces_surjective
  six_post_rejected := completionClock_rejects_six
  nonGray_surjection_rejected :=
    ⟨jumpCover_surjective, jumpCover_not_grayCover, completionClock_rejects_jump⟩

/-! ## The decoy on passes: a closed face is not an item -/

/-- One face of the cube, run once: four ticks, third bit never posted. -/
def facePass : Fin 4 → Pattern 3 :=
  fun t i =>
    if i.val = 2 then false
    else if i.val = 0 then decide (t.val = 1 ∨ t.val = 2)
    else decide (t.val = 2 ∨ t.val = 3)

theorem facePass_third_bit (t : Fin 4) : facePass t ⟨2, by norm_num⟩ = false := by
  simp [facePass]

/-- The face reaches no pattern with the third bit set. -/
theorem facePass_not_surjective : ¬ Function.Surjective facePass := by
  intro h
  obtain ⟨t, ht⟩ := h (fun _ => true)
  have h2 := congrFun ht ⟨2, by norm_num⟩
  rw [facePass_third_bit] at h2
  exact Bool.false_ne_true h2

/-- The face is one post per tick. -/
theorem facePass_onePostPerTick : OnePostPerTick facePass := by
  intro i
  fin_cases i
  · refine ⟨⟨0, by norm_num⟩, ?_, ?_⟩
    · simp [facePass]
    · intro k hk
      fin_cases k <;> simp [facePass] at hk ⊢
  · refine ⟨⟨1, by norm_num⟩, ?_, ?_⟩
    · simp [facePass]
    · intro k hk
      fin_cases k <;> simp [facePass] at hk ⊢
  · refine ⟨⟨0, by norm_num⟩, ?_, ?_⟩
    · simp [facePass]
    · intro k hk
      fin_cases k <;> simp [facePass] at hk ⊢
  · refine ⟨⟨1, by norm_num⟩, ?_, ?_⟩
    · simp [facePass]
    · intro k hk
      fin_cases k <;> simp [facePass] at hk ⊢

/-- **Closure does not complete a recognition.** The face is one post per tick
and returns to its start, and it occupies no item. -/
theorem facePass_not_complete : ¬ CompletionClock facePass :=
  fun h => facePass_not_surjective (completionClock_forces_surjective facePass h)

/-! ## Certificate -/

/-- The clock row closed by definition: coverage derived from the floor step,
the member inhabits the class, the three decoys and the face are rejected, and
the member is extensionally the Gray cover. -/
structure Cert : Prop where
  coverage_derived :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d) (a : Fin d → ℤ),
      PassOccupiesItem pass a ↔ Function.Surjective pass
  member_gray8 : completionClockLaw.completePass grayCycle3Path
  member_rejects_six : ¬ completionClockLaw.completePass balancedSixPostingPass
  member_rejects_jump : ¬ completionClockLaw.completePass jumpCover
  member_rejects_bounce : ¬ completionClockLaw.completePass bouncePass
  face_is_one_post_per_tick_and_no_item :
    OnePostPerTick facePass ∧ ¬ completionClockLaw.completePass facePass
  extensionally_gray_cover :
    ∀ {d T : ℕ} (pass : Fin T → Pattern d),
      completionClockLaw.completePass pass ↔ GrayCoverSemanticModel pass

/-- The certificate holds. -/
theorem cert : Cert where
  coverage_derived := fun pass a => passOccupiesItem_iff_surjective pass a
  member_gray8 := completionClock_gray8
  member_rejects_six := completionClock_rejects_six
  member_rejects_jump := completionClock_rejects_jump
  member_rejects_bounce := completionClock_rejects_bounce
  face_is_one_post_per_tick_and_no_item := ⟨facePass_onePostPerTick, facePass_not_complete⟩
  extensionally_gray_cover := fun pass => completionClock_iff_grayCover pass

end ClockFromCompletion
end KernelClosure
end Foundation
end IndisputableMonolith

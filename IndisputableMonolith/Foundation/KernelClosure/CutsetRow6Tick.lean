import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetHarness

/-!
# Row 6 by cutset: one post per tick is least count

The clock row's process half was the postulate "recognition proceeds by one
post per tick": consecutive states of a pass differ in exactly one bit. The
numeral in it is what a cutset can remove.

## The blade

A *tick* is a step on which something changed (`PatternChange`: the two states differ).
A step is *reducible* when some third state lies strictly between its ends on a
shortest path (`Between`): the clock that takes that step has skipped a state a
finer clock would have posted. The ledger's clock is the *finest* one: every
step is a tick and no step is reducible (`FinestStep`, `FinestClock`). That is a
definition of what the clock is, in words the floor already uses (a distinction
is a bit; a step is a change), and it contains no numeral.

## The theorem

`finestStep_iff_oneBit`: a step is finest exactly when its Hamming distance is
one. The forward direction is least count: a tick has distance at least one; a
distance of two or more admits an intermediate state (flip one differing bit),
so the step is reducible. The numeral "one" in "one post per tick" is the least
positive count (`Cutset.least_positive_count`), derived.

`finestClock_iff_onePostPerTick`: on passes the two predicates agree, so the
process postulate is the finest-clock definition.

## The violators

* `jumpCover`: the two-bit step `00 → 11` skips the state `10`, exhibited
  (`jumpCover_skips`). Not finest.
* `stutterPass`: a step on which nothing changes. Not a tick, not finest.

## Verdict

The one-post-per-tick clause moves from process postulate to: a definition
(the ledger's clock is the finest recognizer of change) plus a theorem (the
finest change is one bit). MODEL under the definition; the numeral is derived.
What remains a premise is that the ledger has a clock at all, that recognition
proceeds in steps.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row6Tick

open Patterns PublicSpine.ClockDischargeProbe ClockFromCompletion

variable {d : ℕ}

/-! ## Hamming distance -/

/-- The number of bits on which two patterns differ. -/
def hamming (p q : Pattern d) : ℕ :=
  (Finset.univ.filter (fun i => p i ≠ q i)).card

theorem hamming_eq_zero_iff (p q : Pattern d) : hamming p q = 0 ↔ p = q := by
  unfold hamming
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    funext i
    by_contra hne
    exact h (Finset.mem_univ i) hne
  · intro h i _ hne
    exact hne (congrFun h i)

/-- One-bit difference is Hamming distance one. -/
theorem oneBitDiff_iff_hamming_one (p q : Pattern d) : OneBitDiff p q ↔ hamming p q = 1 := by
  unfold OneBitDiff hamming
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨k, hk, huniq⟩
    refine ⟨k, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => huniq i h, fun h => h ▸ hk⟩
  · rintro ⟨k, hk⟩
    have hmem : ∀ i, p i ≠ q i ↔ i = k := by
      intro i
      have := Finset.ext_iff.mp hk i
      simpa using this
    exact ⟨k, (hmem k).2 rfl, fun i hi => (hmem i).1 hi⟩

/-- Flipping one differing bit of `p` toward `q` moves distance one from `p`. -/
theorem hamming_update_left (p q : Pattern d) (k : Fin d) (hk : p k ≠ q k) :
    hamming p (Function.update p k (q k)) = 1 := by
  rw [← oneBitDiff_iff_hamming_one]
  refine ⟨k, ?_, ?_⟩
  · simpa using hk
  · intro i hi
    by_contra hne
    rw [Function.update_of_ne hne] at hi
    exact hi rfl

/-- Flipping one differing bit of `p` toward `q` moves distance one closer to `q`. -/
theorem hamming_update_right (p q : Pattern d) (k : Fin d) (hk : p k ≠ q k) :
    hamming (Function.update p k (q k)) q + 1 = hamming p q := by
  unfold hamming
  have hset : Finset.univ.filter (fun i => Function.update p k (q k) i ≠ q i)
      = (Finset.univ.filter (fun i => p i ≠ q i)).erase k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hik : i = k
    · subst hik
      simp
    · rw [Function.update_of_ne hik]
      exact ⟨fun h => ⟨hik, h⟩, fun h => h.2⟩
  rw [hset, Finset.card_erase_add_one]
  simpa using hk

/-! ## PatternChange, reducibility, the finest step -/

/-- A tick: the step changes something. -/
def PatternChange (p q : Pattern d) : Prop := p ≠ q

/-- `m` lies strictly between `p` and `q` on a shortest path: a state the step
from `p` to `q` skipped. -/
def Between (p m q : Pattern d) : Prop :=
  m ≠ p ∧ m ≠ q ∧ hamming p m + hamming m q = hamming p q

/-- A finest step: a tick that no state subdivides. -/
def FinestStep (p q : Pattern d) : Prop :=
  PatternChange p q ∧ ¬ ∃ m, Between p m q

/-- A tick has distance at least one: the least positive count. -/
theorem tick_hamming_pos (p q : Pattern d) (h : PatternChange p q) : 0 < hamming p q :=
  Nat.pos_of_ne_zero (fun h0 => h ((hamming_eq_zero_iff p q).1 h0))

/-- **The finest step is one bit.** Least count on the tick, and the intermediate
state exhibited for every longer step. -/
theorem finestStep_iff_oneBit (p q : Pattern d) : FinestStep p q ↔ OneBitDiff p q := by
  rw [oneBitDiff_iff_hamming_one]
  constructor
  · rintro ⟨hne, hirr⟩
    have hpos := tick_hamming_pos p q hne
    by_contra hone
    have h2 : 2 ≤ hamming p q := by omega
    have hex : ∃ k, p k ≠ q k := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    obtain ⟨k, hk⟩ := hex
    apply hirr
    refine ⟨Function.update p k (q k), ?_, ?_, ?_⟩
    · intro hm
      have h1 := hamming_update_left p q k hk
      rw [hm, (hamming_eq_zero_iff p p).2 rfl] at h1
      omega
    · intro hm
      have h1 := hamming_update_right p q k hk
      rw [hm, (hamming_eq_zero_iff q q).2 rfl] at h1
      omega
    · rw [hamming_update_left p q k hk, add_comm]
      exact hamming_update_right p q k hk
  · intro h1
    refine ⟨?_, ?_⟩
    · intro heq
      rw [(hamming_eq_zero_iff p q).2 heq] at h1
      omega
    · rintro ⟨m, hmp, hmq, hsum⟩
      rw [h1] at hsum
      have : hamming p m = 0 ∨ hamming m q = 0 := by omega
      rcases this with h | h
      · exact hmp ((hamming_eq_zero_iff p m).1 h).symm
      · exact hmq ((hamming_eq_zero_iff m q).1 h)

/-! ## The finest clock -/

/-- The ledger's clock is the finest recognizer of change: every step is a
finest step. -/
def FinestClock {T : ℕ} [NeZero T] (pass : Fin T → Pattern d) : Prop :=
  ∀ i : Fin T, FinestStep (pass i) (pass (i + 1))

/-- **The process postulate is the finest-clock definition.** -/
theorem finestClock_iff_onePostPerTick {T : ℕ} [NeZero T] (pass : Fin T → Pattern d) :
    FinestClock pass ↔ OnePostPerTick pass :=
  forall_congr' (fun i => finestStep_iff_oneBit _ _)

theorem gray8_finest : FinestClock grayCycle3Path := by
  obtain ⟨_, h1, _⟩ := completionClock_gray8
  exact (finestClock_iff_onePostPerTick _).2 h1

/-! ## The violators -/

/-- The state the jump cover skipped. -/
def pat10 : Pattern 2 := fun j => decide (j.val = 0)

/-- `00 → 11` skips `10`: the two-bit step is reducible. -/
theorem jumpCover_skips : Between pat00 pat10 pat11 := by
  unfold Between
  decide

theorem jumpCover_not_finest : ¬ FinestClock jumpCover := by
  intro h
  have h0 := (finestStep_iff_oneBit _ _).1 (h 0)
  have hnot : ¬ OneBitDiff (jumpCover 0) (jumpCover 1) := by
    simpa [jumpCover] using pat00_pat11_not_oneBit
  exact hnot h0

/-- A pass on which nothing changes. -/
def stutterPass : Fin 2 → Pattern 3 := fun _ => bounceA

theorem stutterPass_not_finest : ¬ FinestClock stutterPass :=
  fun h => (h 0).1 rfl

theorem stutterPass_not_onePost : ¬ OnePostPerTick stutterPass :=
  fun h => stutterPass_not_finest ((finestClock_iff_onePostPerTick _).2 h)

/-! ## The row -/

/-- The jump cover as a candidate. -/
def jump : Pass := ⟨2, 4, jumpCover⟩

/-- Row 6 in harness form. -/
def row : CutsetRow Pass where
  Floor := fun x => 0 < x.2.1
  Sentence := fun x => ∃ h : NeZero x.2.1, @OnePostPerTick x.1 x.2.1 h x.2.2
  Blade := fun x => ∃ h : NeZero x.2.1, @FinestClock x.1 x.2.1 h x.2.2
  provenance := .definition "tick = a change no state subdivides; the clock is the finest recognizer of change"
  real := gray8
  real_floor := Nat.succ_pos 7
  blade_real := ⟨⟨Nat.succ_ne_zero 7⟩, gray8_finest⟩
  violator := jump
  violator_floor := Nat.succ_pos 3
  violator_violates := by
    rintro ⟨h, hop⟩
    have hnot : ¬ OneBitDiff (jumpCover 0) (jumpCover 1) := by
      simpa [jumpCover] using pat00_pat11_not_oneBit
    exact hnot (hop 0)
  blade_kills_violator := by
    rintro ⟨h, hf⟩
    exact jumpCover_not_finest hf
  exclusion := fun _ _ hs hb =>
    hs (hb.imp fun _ hf => (finestClock_iff_onePostPerTick _).1 hf)

/-! ## Certificate -/

structure Cert : Prop where
  finest_iff_one_bit : ∀ {d : ℕ} (p q : Pattern d), FinestStep p q ↔ OneBitDiff p q
  clock_iff_process :
    ∀ {d T : ℕ} [NeZero T] (pass : Fin T → Pattern d), FinestClock pass ↔ OnePostPerTick pass
  gray8_finest : FinestClock grayCycle3Path
  jump_skips_a_state : Between pat00 pat10 pat11
  jump_not_finest : ¬ FinestClock jumpCover
  stutter_not_finest : ¬ FinestClock stutterPass
  row_forces : ∀ x : Pass, row.Floor x → row.Blade x → row.Sentence x
  row_class_nonempty : ∃ x : Pass, row.Floor x ∧ ¬ row.Sentence x

theorem cert : Cert where
  finest_iff_one_bit := fun p q => finestStep_iff_oneBit p q
  clock_iff_process := fun pass => finestClock_iff_onePostPerTick pass
  gray8_finest := gray8_finest
  jump_skips_a_state := jumpCover_skips
  jump_not_finest := jumpCover_not_finest
  stutter_not_finest := stutterPass_not_finest
  row_forces := row.forces
  row_class_nonempty := row.class_nonempty

end Row6Tick
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith

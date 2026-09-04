import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow6Tick

/-!
# Cutset row 6, promoted: the clock is the post sequence

Row 6 (`CutsetRow6Tick`) closed "one post per tick" under a definition: the
clock is the finest recognizer of change. Two violators were excluded by that
word: the stutter (a tick on which nothing changes) and the jump (a tick on
which two bits change). This module asks what each alternative *is* to the
ledger.

## The stutter is impossible

A tick is a change (`PatternChange p q := p ≠ q`). A step on which no bit posts is no
change (`tick_iff_not_recognitionFree`, pattern extensionality, the same floor
theorem as `CutsetRow5Ledger`). So a "tick" with equal endpoints is not a tick
at all; the stutter is excluded by a floor theorem, not by a word.

## The jump is a coarsening, not a clock of its own

Every tick, of any Hamming distance `n`, is a run of exactly `n` posts: there is
a one-post path from `p` to `q` of length `hamming p q` (`exists_post_path`).
So a pass whose ticks change several bits is a sampling of a one-post pass: the
same posts, read fewer at a time. The post sequence is the finest clock, and
every other clock is a subsequence of it.

The coarse reading loses information the ledger has. A two-bit tick has two
distinct one-post refinements, one per order of the flips
(`two_bit_two_orders`): the coarse clock does not know which bit posted first.
And the coarse clock is not parameter-free: it needs a rule for which posts to
read (every second post, every eighth), and that rule is a number the ledger
never posted. The post sequence needs no such rule.

## Status

The stutter alternative is impossible (floor theorem). The jump alternative is
not a distinct ledger: it is the same post sequence sampled by an un-derived
rule, with the order of posts lost. "The clock is the finest recognizer of
change" therefore reads: the ledger's clock is its own sequence of posts. What
remains of the definition is the identification of the theory's clock with that
sequence rather than with a sampling of it; the sampling would cost a parameter.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row6Ledger

open Patterns PublicSpine.ClockDischargeProbe ClockFromCompletion Row6Tick

variable {d : ℕ}

/-! ## The stutter -/

/-- No post between two states. -/
def RecognitionFree (p q : Pattern d) : Prop := ∀ i, p i = q i

/-- **Floor theorem.** A tick is exactly a step that posts a bit. -/
theorem tick_iff_not_recognitionFree (p q : Pattern d) :
    PatternChange p q ↔ ¬ RecognitionFree p q := by
  unfold PatternChange RecognitionFree
  constructor
  · intro hne hfree
    exact hne (funext hfree)
  · intro h heq
    exact h (fun i => by rw [heq])

/-- The stutter's step posts nothing, so it is not a tick. -/
theorem stutter_step_recognitionFree : RecognitionFree (stutterPass 0) (stutterPass 1) :=
  fun _ => rfl

theorem stutter_step_not_tick : ¬ PatternChange (stutterPass 0) (stutterPass 1) :=
  (tick_iff_not_recognitionFree _ _).not.mpr (not_not.mpr stutter_step_recognitionFree)

/-! ## Every tick is a run of posts -/

/-- A one-post path from `p` to `q` of length `hamming p q`. -/
theorem exists_post_path_aux :
    ∀ (n : ℕ) (p q : Pattern d), hamming p q = n →
      ∃ path : Fin (n + 1) → Pattern d,
        path 0 = p ∧ path (Fin.last n) = q ∧
        ∀ i : Fin n, OneBitDiff (path i.castSucc) (path i.succ)
  | 0, p, q, h => by
      have hpq : p = q := (hamming_eq_zero_iff p q).1 h
      refine ⟨fun _ => p, rfl, hpq, fun i => i.elim0⟩
  | n + 1, p, q, h => by
      have hpos : 0 < hamming p q := by omega
      have hex : ∃ k, p k ≠ q k := by
        by_contra hall
        push_neg at hall
        have : hamming p q = 0 := (hamming_eq_zero_iff p q).2 (funext hall)
        omega
      obtain ⟨k, hk⟩ := hex
      have hstep : OneBitDiff p (Function.update p k (q k)) := by
        rw [oneBitDiff_iff_hamming_one]
        exact hamming_update_left p q k hk
      have hrest : hamming (Function.update p k (q k)) q = n := by
        have := hamming_update_right p q k hk
        omega
      obtain ⟨path', h0, hlast, hsteps⟩ := exists_post_path_aux n (Function.update p k (q k)) q hrest
      refine ⟨Fin.cons p path', ?_, ?_, ?_⟩
      · simp
      · rw [← Fin.succ_last, Fin.cons_succ]
        exact hlast
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one]
          have : (Fin.cons p path' : Fin (n + 2) → Pattern d) 1 = path' 0 := by
            rw [show (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ from rfl, Fin.cons_succ]
          rw [this, h0]
          exact hstep
        · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact hsteps j

/-- **Every tick is a run of posts.** A step of Hamming distance `n` is `n`
posts in a row. -/
theorem exists_post_path (p q : Pattern d) :
    ∃ path : Fin (hamming p q + 1) → Pattern d,
      path 0 = p ∧ path (Fin.last _) = q ∧
      ∀ i : Fin (hamming p q), OneBitDiff (path i.castSucc) (path i.succ) :=
  exists_post_path_aux _ p q rfl

/-! ## The coarse clock forgets the order of posts -/

/-- The other intermediate state of the jump: `01`. -/
def pat01 : Pattern 2 := fun j => decide (j.val = 1)

theorem pat10_ne_pat01 : pat10 ≠ pat01 := by
  intro h
  have := congrFun h 0
  simp [pat10, pat01] at this

/-- `00 → 10 → 11` and `00 → 01 → 11` are both one-post refinements of the
jump's first tick, and they differ. The coarse clock cannot tell them apart. -/
theorem two_bit_two_orders :
    (OneBitDiff (jumpCover 0) pat10 ∧ OneBitDiff pat10 (jumpCover 1)) ∧
    (OneBitDiff (jumpCover 0) pat01 ∧ OneBitDiff pat01 (jumpCover 1)) ∧
    pat10 ≠ pat01 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, pat10_ne_pat01⟩ <;>
    first
    | exact pat10_ne_pat01
    | (rw [oneBitDiff_iff_hamming_one]; decide)

/-! ## Certificate -/

structure RowCert : Prop where
  /-- A tick is a step that posts a bit. -/
  tick_is_post : ∀ {d : ℕ} (p q : Pattern d), PatternChange p q ↔ ¬ RecognitionFree p q
  /-- The stutter is not a tick: impossible, by the floor theorem. -/
  stutter_impossible : ¬ PatternChange (stutterPass 0) (stutterPass 1)
  /-- Every tick of distance `n` is `n` posts: the coarse clock samples the fine one. -/
  every_tick_is_posts : ∀ {d : ℕ} (p q : Pattern d),
    ∃ path : Fin (hamming p q + 1) → Pattern d,
      path 0 = p ∧ path (Fin.last _) = q ∧
      ∀ i : Fin (hamming p q), OneBitDiff (path i.castSucc) (path i.succ)
  /-- The coarse clock loses the order of posts. -/
  coarse_forgets_order :
    (OneBitDiff (jumpCover 0) pat10 ∧ OneBitDiff pat10 (jumpCover 1)) ∧
    (OneBitDiff (jumpCover 0) pat01 ∧ OneBitDiff pat01 (jumpCover 1)) ∧
    pat10 ≠ pat01
  /-- The finest clock is exactly the post sequence. -/
  finest_is_posts : ∀ {d T : ℕ} [NeZero T] (pass : Fin T → Pattern d),
    FinestClock pass ↔ OnePostPerTick pass

theorem cert : RowCert where
  tick_is_post := fun p q => tick_iff_not_recognitionFree p q
  stutter_impossible := stutter_step_not_tick
  every_tick_is_posts := fun p q => exists_post_path p q
  coarse_forgets_order := two_bit_two_orders
  finest_is_posts := fun pass => finestClock_iff_onePostPerTick pass

end Row6Ledger
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith

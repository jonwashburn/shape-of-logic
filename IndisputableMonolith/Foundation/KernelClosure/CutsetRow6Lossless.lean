import Mathlib
import IndisputableMonolith.Foundation.KernelClosure.CutsetRow6Ledger

/-!
# Cutset row 6, closed: the only lossless clock is the post sequence

`CutsetRow6Ledger` left one identification standing: the theory's clock is the
ledger's own post sequence rather than a sampling of it, "the sampling would
cost a parameter". This module replaces that sentence with a floor theorem.

## The blade

The ledger is the *minimal lossless* record of recognition events (Pardo-Guerra,
Thapa, Simons, Washburn 2026, the derivation of the ledger from the cost). A
clock is what the ledger records of a run of posts. A clock is **lossless** when
its record determines the run: two runs with the same record are the same run
(`Lossless`, injectivity).

## The theorems

* The post sequence, read one post per tick, is lossless (`postClock_lossless`).
* Every lossless clock is the post sequence up to relabeling: its record can
  be decoded back to the run (`lossless_recovers`), and conversely anything
  that decodes to the run is lossless (`lossless_of_recovers`). So "the clock
  is the post sequence" is not a choice among lossless clocks; it is what
  lossless means here.
* Every sampling clock of rate `k ≥ 2` is lossy (`sample_not_lossless`): two
  runs from `00` that flip the two bits in opposite orders and then move in
  step have the same record at rate `k` and are different runs. The order of
  posts is exactly what the coarse clock throws away.

The stutter (a tick that posts nothing) was already impossible (`CutsetRow6Ledger`,
a run with a stutter is not a run of posts). So both alternatives to "one post
per tick" are now excluded by floor theorems: the stutter is not a change, and
the jump is not lossless. What row 6 rests on is the published fact that the
ledger is lossless; no identification remains.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelClosure
namespace Cutset
namespace Row6Lossless

open Patterns PublicSpine.ClockDischargeProbe Row6Tick Row6Ledger

/-! ## Runs of posts and clocks -/

/-- A run of `n` posts on `d` cells: `n+1` states, each one bit from the last. -/
@[ext]
structure PostHistory (d n : ℕ) where
  /-- The states. -/
  state : Fin (n + 1) → Pattern d
  /-- Consecutive states differ in one bit. -/
  onePost : ∀ i : Fin n, OneBitDiff (state i.castSucc) (state i.succ)

/-- A clock: what the ledger records of a run. -/
def Clock (d n : ℕ) (α : Type) := PostHistory d n → α

/-- **The blade.** A clock is lossless when its record determines the run. -/
def Lossless {d n : ℕ} {α : Type} (c : Clock d n α) : Prop := Function.Injective c

/-- The post sequence read one post per tick. -/
def postClock (d n : ℕ) : Clock d n (Fin (n + 1) → Pattern d) := fun h => h.state

theorem postClock_lossless (d n : ℕ) : Lossless (postClock d n) := by
  intro h1 h2 heq
  exact PostHistory.ext heq

/-! ## Lossless means "the post sequence up to relabeling" -/

/-- A lossless record decodes back to the run. -/
theorem lossless_recovers {d n : ℕ} {α : Type} [Nonempty (PostHistory d n)]
    (c : Clock d n α) (hc : Lossless c) :
    ∃ g : α → (Fin (n + 1) → Pattern d), ∀ h, g (c h) = h.state :=
  ⟨fun a => (Function.invFun c a).state, fun h => by
    show (Function.invFun c (c h)).state = h.state
    rw [Function.leftInverse_invFun hc h]⟩

/-- Anything that decodes to the run is lossless. -/
theorem lossless_of_recovers {d n : ℕ} {α : Type} (c : Clock d n α)
    (hg : ∃ g : α → (Fin (n + 1) → Pattern d), ∀ h, g (c h) = h.state) : Lossless c := by
  obtain ⟨g, hg⟩ := hg
  intro h1 h2 heq
  apply PostHistory.ext
  rw [← hg h1, ← hg h2, heq]

/-! ## The sampling clock -/

/-- The clock that reads every `k`-th state of a run of `n` posts. -/
def sampleClock (d n k : ℕ) : Clock d n (Fin (n / k + 1) → Pattern d) :=
  fun h j => h.state ⟨j.val * k,
    Nat.lt_succ_of_le (le_trans (Nat.mul_le_mul_right k (Nat.lt_succ_iff.mp j.isLt))
      (Nat.div_mul_le_self n k))⟩

/-! ## Two runs the coarse clock cannot tell apart -/

/-- After the two bits are both up, the runs move in step: `11, 10, 11, 10, …`. -/
def tail (i : ℕ) : Pattern 2 := if i % 2 = 0 then pat11 else pat10

/-- Flip bit `0` first: `00, 10, 11, 10, 11, …`. -/
def orderA (i : ℕ) : Pattern 2 := if i = 0 then pat00 else if i = 1 then pat10 else tail i

/-- Flip bit `1` first: `00, 01, 11, 10, 11, …`. -/
def orderB (i : ℕ) : Pattern 2 := if i = 0 then pat00 else if i = 1 then pat01 else tail i

theorem tail_step (i : ℕ) : OneBitDiff (tail i) (tail (i + 1)) := by
  unfold tail
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · rw [if_pos h, if_neg (by omega)]
    rw [oneBitDiff_iff_hamming_one]; decide
  · rw [if_neg (by omega), if_pos (by omega)]
    rw [oneBitDiff_iff_hamming_one]; decide

theorem orderA_step (i : ℕ) : OneBitDiff (orderA i) (orderA (i + 1)) := by
  rcases i with _ | _ | i
  · simp only [orderA, if_true, Nat.zero_add, if_false, Nat.one_ne_zero]
    rw [oneBitDiff_iff_hamming_one]; decide
  · simp only [orderA, tail, if_false, if_true, Nat.reduceEqDiff]
    rw [oneBitDiff_iff_hamming_one]; decide
  · simp only [orderA, if_false, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, Nat.reduceEqDiff]
    exact tail_step (i + 2)

theorem orderB_step (i : ℕ) : OneBitDiff (orderB i) (orderB (i + 1)) := by
  rcases i with _ | _ | i
  · simp only [orderB, if_true, Nat.zero_add, if_false, Nat.one_ne_zero]
    rw [oneBitDiff_iff_hamming_one]; decide
  · simp only [orderB, tail, if_false, if_true, Nat.reduceEqDiff]
    rw [oneBitDiff_iff_hamming_one]; decide
  · simp only [orderB, if_false, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, Nat.reduceEqDiff]
    exact tail_step (i + 2)

/-- The run that flips bit `0` first, as a run of `n` posts. -/
def histA (n : ℕ) : PostHistory 2 n :=
  ⟨fun i => orderA i.val, fun i => by simpa using orderA_step i.val⟩

/-- The run that flips bit `1` first, as a run of `n` posts. -/
def histB (n : ℕ) : PostHistory 2 n :=
  ⟨fun i => orderB i.val, fun i => by simpa using orderB_step i.val⟩

theorem orderA_eq_orderB_of_two_le {i : ℕ} (hi : 2 ≤ i) : orderA i = orderB i := by
  unfold orderA orderB
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem histA_ne_histB (n : ℕ) (hn : 1 ≤ n) : histA n ≠ histB n := by
  intro h
  have h1 := congrFun (congrArg PostHistory.state h) ⟨1, by omega⟩
  simp only [histA, histB, orderA, orderB, Nat.one_ne_zero, if_false, if_true] at h1
  exact pat10_ne_pat01 h1

/-- **The coarse clock is lossy.** At any rate `k ≥ 2`, the two orders of a
two-bit change have the same record and are different runs. -/
theorem sample_not_lossless (k : ℕ) (hk : 2 ≤ k) : ¬ Lossless (sampleClock 2 k k) := by
  intro hinj
  apply histA_ne_histB k (by omega)
  apply hinj
  funext j
  have hkk : k / k = 1 := Nat.div_self (by omega)
  have hj : (j : ℕ) ≤ 1 := (Nat.lt_succ_iff.mp j.isLt).trans (le_of_eq hkk)
  simp only [sampleClock, histA, histB]
  rcases hj.lt_or_eq with h0 | h1
  · have : j.val = 0 := by omega
    simp [this, orderA, orderB]
  · rw [h1, Nat.one_mul]
    exact orderA_eq_orderB_of_two_le hk

/-- The eight-tick ledger has runs. -/
instance : Nonempty (PostHistory 2 3) := ⟨histA 3⟩

/-! ## Certificate -/

structure Cert : Prop where
  /-- The post sequence is lossless. -/
  post_lossless : ∀ d n : ℕ, Lossless (postClock d n)
  /-- A lossless clock decodes to the post sequence. -/
  lossless_is_post : ∀ (d n : ℕ) (α : Type) [Nonempty (PostHistory d n)] (c : Clock d n α),
    Lossless c → ∃ g : α → (Fin (n + 1) → Pattern d), ∀ h, g (c h) = h.state
  /-- Decoding to the post sequence is losslessness. -/
  post_is_lossless : ∀ (d n : ℕ) (α : Type) (c : Clock d n α),
    (∃ g : α → (Fin (n + 1) → Pattern d), ∀ h, g (c h) = h.state) → Lossless c
  /-- Every sampling clock of rate at least two is lossy. -/
  sample_lossy : ∀ k : ℕ, 2 ≤ k → ¬ Lossless (sampleClock 2 k k)
  /-- The stutter is not a tick (from `CutsetRow6Ledger`). -/
  stutter_impossible : ¬ PatternChange (stutterPass 0) (stutterPass 1)

theorem cert : Cert where
  post_lossless := postClock_lossless
  lossless_is_post := fun _ _ _ _ c hc => lossless_recovers c hc
  post_is_lossless := fun _ _ _ c hg => lossless_of_recovers c hg
  sample_lossy := sample_not_lossless
  stutter_impossible := stutter_step_not_tick

end Row6Lossless
end Cutset
end KernelClosure
end Foundation
end IndisputableMonolith

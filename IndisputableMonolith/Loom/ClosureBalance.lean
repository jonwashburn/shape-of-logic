import Mathlib
import IndisputableMonolith.Loom.LoopSpace

/-!
# Closure is double-entry balance on the window

A completed recognition event is a closed walk: the history returns to its
starting state (`Walk.Closed`). This module proves that closure is exactly
per-axis posting balance: the walk returns iff every axis is flipped an even
number of times, so each distinction's postings cancel in pairs.

At the window level, "the event completes" and "the books balance" are one
predicate. The Alphabet's premise that completed events are the closed walks
is therefore not an extra postulate on top of double entry: it is double
entry, read on the window.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Loom
namespace ClosureBalance

open IndisputableMonolith.Patterns

/-- Where axis `i` ends up after a walk: unchanged when the walk flips `i` an
even number of times, negated when odd. Order of steps is irrelevant to each
coordinate, which is what makes the balance reading exact. -/
theorem foldl_flip_apply {d : ℕ} (p : Pattern d) (L : List (Fin d)) (i : Fin d) :
    L.foldl flip p i = if Even (L.count i) then p i else !(p i) := by
  induction L generalizing p with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih (flip p a)]
    rcases eq_or_ne i a with h | h
    · subst h
      have hc : (i :: L).count i = L.count i + 1 := by simp
      have hf : flip p i i = !(p i) := by simp [flip]
      rw [hc, hf]
      by_cases he : Even (L.count i) <;> simp [he, Nat.even_add_one]
    · have hc : (a :: L).count i = L.count i := by
        simp [Ne.symm h]
      have hf : flip p a i = p i := by simp [flip, h]
      rw [hc, hf]

/-- **Closure is balance.** A history returns to its start iff every axis is
flipped an even number of times: the per-axis postings cancel in pairs. -/
theorem closed_iff_balanced {d : ℕ} (w : Walk d) :
    w.Closed ↔ ∀ i : Fin d, Even (w.steps.count i) := by
  unfold Walk.Closed Walk.endpoint
  constructor
  · intro h i
    have hi := congrFun h i
    rw [foldl_flip_apply] at hi
    by_contra he
    rw [if_neg he] at hi
    cases hp : w.start i <;> rw [hp] at hi <;> simp at hi
  · intro h
    funext i
    rw [foldl_flip_apply, if_pos (h i)]

/-- The window instance (`d = 3`): a completed event on the recognition
window is exactly a per-axis balanced posting record. -/
theorem closed_iff_balanced_window (w : Walk 3) :
    w.Closed ↔ ∀ i : Fin 3, Even (w.steps.count i) :=
  closed_iff_balanced w

end ClosureBalance
end Loom
end IndisputableMonolith

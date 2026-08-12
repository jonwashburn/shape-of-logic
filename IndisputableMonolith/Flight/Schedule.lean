import Mathlib
import IndisputableMonolith.Spiral.SpiralField

/-!
# Flight Scheduling (8-tick control discipline)

This file defines a minimal control/schedule surface and reuses the existing
8-window neutrality predicates from `SpiralField`.
-/

namespace IndisputableMonolith
namespace Flight
namespace Schedule

open scoped BigOperators

open IndisputableMonolith.Spiral

/-- Minimal control datum per tick.

This is intentionally small; hardware-level specs will refine this later.
-/
structure Control where
  pulse : Bool
  deriving Repr

/-- A drive schedule is a tick-indexed control stream. -/
abbrev DriveSchedule := ℕ → Control

/-- Re-export: 8-gate neutrality predicate. -/
abbrev eightGateNeutral := SpiralField.eightGateNeutral

/-- Re-export: 8-gate neutrality score (diagnostic). -/
abbrev neutralityScore := SpiralField.neutralityScore

/-- Shift lemma for the neutrality score: shifting the start index shifts the sampled window. -/
lemma neutralityScore_succ (w : ℕ → ℝ) (t0 : ℕ) :
    neutralityScore w (t0 + 1) = (Finset.range 8).sum (fun k => w (t0 + 1 + k)) := by
  rfl

/-- Simple 8-periodicity predicate (for “8-phase schedules”). -/
def Periodic8 (w : ℕ → ℝ) : Prop := ∀ t, w (t + 8) = w t

lemma neutralityScore_shift1_of_periodic8 (w : ℕ → ℝ) (t0 : ℕ) (hper : Periodic8 w) :
    neutralityScore w (t0 + 1) = neutralityScore w t0 := by
  classical
  -- Expand both scores as sums over 8 consecutive ticks.
  unfold neutralityScore SpiralField.neutralityScore
  -- Use periodicity to rewrite the last term `w (t0+8)` into `w t0`.
  have hw8 : w (t0 + 8) = w t0 := by
    simpa [Periodic8, Nat.add_assoc] using hper t0

  -- LHS: split off the last element (k=7), so we can rewrite it using periodicity.
  have hL :
      (Finset.range 8).sum (fun k => w (t0 + 1 + k))
        =
        (Finset.range 7).sum (fun k => w (t0 + 1 + k)) + w (t0 + 8) := by
    -- `sum_range_succ` peels off the last term at index `7`.
    simpa [Finset.sum_range_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Finset.sum_range_succ (fun k => w (t0 + 1 + k)) 7)

  -- RHS: peel off the *first* element (k=0) via `sum_range_succ'`.
  have hR :
      (Finset.range 7).sum (fun k => w (t0 + (k + 1))) + w (t0 + 0)
        =
        (Finset.range 8).sum (fun k => w (t0 + k)) := by
    -- `sum_range_succ'` states the reverse direction; we use `.symm`.
    simpa [Finset.sum_range_succ', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Finset.sum_range_succ' (fun k => w (t0 + k)) 7).symm

  -- Normalize the 7-term sums: `t0 + 1 + k = t0 + (k + 1)`.
  have hsum7 :
      (Finset.range 7).sum (fun k => w (t0 + 1 + k))
        =
        (Finset.range 7).sum (fun k => w (t0 + (k + 1))) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

  -- Put it together.
  calc
    (Finset.range 8).sum (fun k => w (t0 + 1 + k))
        = (Finset.range 7).sum (fun k => w (t0 + 1 + k)) + w (t0 + 8) := hL
    _ = (Finset.range 7).sum (fun k => w (t0 + (k + 1))) + w t0 := by
          simp [hsum7, hw8]
    _ = (Finset.range 7).sum (fun k => w (t0 + (k + 1))) + w (t0 + 0) := by
          simp
    _ = (Finset.range 8).sum (fun k => w (t0 + k)) := hR

/-- Main schedule-shift invariant: if the signal is 8-periodic, the 8-gate sum is invariant under a shift. -/
theorem eightGateNeutral_shift_invariance (w : ℕ → ℝ) (t0 : ℕ) (hper : Periodic8 w) :
    eightGateNeutral w t0 ↔ eightGateNeutral w (t0 + 1) := by
  unfold eightGateNeutral SpiralField.eightGateNeutral
  constructor <;> intro h
  · -- forward direction
    have hs : neutralityScore w (t0 + 1) = neutralityScore w t0 :=
      neutralityScore_shift1_of_periodic8 w t0 hper
    have h0 : neutralityScore w t0 = 0 := by
      simpa [SpiralField.neutralityScore] using h
    have : neutralityScore w (t0 + 1) = 0 := by simpa [hs] using h0
    simpa [SpiralField.neutralityScore] using this
  · -- backward direction (symmetry)
    have hs : neutralityScore w (t0 + 1) = neutralityScore w t0 :=
      neutralityScore_shift1_of_periodic8 w t0 hper
    have h1 : neutralityScore w (t0 + 1) = 0 := by
      simpa [SpiralField.neutralityScore] using h
    have : neutralityScore w t0 = 0 := by simpa [hs] using h1
    simpa [SpiralField.neutralityScore] using this

end Schedule
end Flight
end IndisputableMonolith


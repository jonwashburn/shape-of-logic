import Mathlib

namespace IndisputableMonolith

/-!
Pattern and Measurement layers: streams, windows, and aligned block sums.
This file ports the PatternLayer/MeasurementLayer cluster from the umbrella.
-/

namespace PatternLayer

open scoped BigOperators
open Finset

/-- Boolean stream as an infinite display. -/
def Stream := Nat → Bool

/-- A finite window/pattern of length `n`. -/
def Pattern (n : Nat) := Fin n → Bool

/-- Integer functional `Z` counting ones in a finite window. -/
def Z_of_window {n : Nat} (w : Pattern n) : Nat :=
  ∑ i : Fin n, (if w i then 1 else 0)

/-- The cylinder set of streams whose first `n` bits coincide with the window `w`. -/
def Cylinder {n : Nat} (w : Pattern n) : Set Stream :=
  { s | ∀ i : Fin n, s i.val = w i }

/-- Periodic extension of an 8‑bit window. -/
def extendPeriodic8 (w : Pattern 8) : Stream := fun t =>
  let i : Fin 8 := ⟨t % 8, Nat.mod_lt _ (by decide)⟩
  w i

/-- Sum of the first `m` bits of a stream. -/
def sumFirst (m : Nat) (s : Stream) : Nat :=
  ∑ i : Fin m, (if s i.val then 1 else 0)

/-- If a stream agrees with a window on its first `n` bits, then the first‑`n` sum equals `Z`. -/
lemma sumFirst_eq_Z_on_cylinder {n : Nat} (w : Pattern n)
  {s : Stream} (hs : s ∈ Cylinder w) :
  sumFirst n s = Z_of_window w := by
  classical
  unfold sumFirst Z_of_window Cylinder at *
  have : (fun i : Fin n => (if s i.val then 1 else 0)) =
         (fun i : Fin n => (if w i then 1 else 0)) := by
    funext i; simpa [hs i]
  simpa [this]

/-- For an 8‑bit window extended periodically, the first‑8 sum equals `Z`. -/
lemma sumFirst8_extendPeriodic_eq_Z (w : Pattern 8) :
  sumFirst 8 (extendPeriodic8 w) = Z_of_window w := by
  classical
  unfold sumFirst Z_of_window extendPeriodic8
  have hmod : ∀ i : Fin 8, (i.val % 8) = i.val := by
    intro i; exact Nat.mod_eq_of_lt i.isLt
  have hfun :
    (fun i : Fin 8 => (if w ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩ then 1 else 0))
    = (fun i : Fin 8 => (if w i then 1 else 0)) := by
      funext i; simp [hmod i]
  have := congrArg (fun f => ∑ i : Fin 8, f i) hfun
  simpa using this

end PatternLayer

namespace MeasurementLayer

open scoped BigOperators
open Finset PatternLayer

/-- Sum of one 8‑tick sub‑block starting at index `j*8`. -/
def subBlockSum8 (s : Stream) (j : Nat) : Nat :=
  ∑ i : Fin 8, (if s (j * 8 + i.val) then 1 else 0)

/-- Aligned block sum over `k` copies of the 8‑tick window (so instrument length `T=8k`). -/
def blockSumAligned8 (k : Nat) (s : Stream) : Nat :=
  ∑ j : Fin k, subBlockSum8 s j.val

/-- On any stream lying in the cylinder of an 8‑bit window, the aligned
    first block sum (j=0; T=8k alignment) equals the window integer `Z`. -/
lemma firstBlockSum_eq_Z_on_cylinder (w : Pattern 8) {s : Stream}
  (hs : s ∈ PatternLayer.Cylinder w) :
  subBlockSum8 s 0 = Z_of_window w := by
  classical
  have hsum : subBlockSum8 s 0 = PatternLayer.sumFirst 8 s := by
    unfold subBlockSum8 PatternLayer.sumFirst
    simp [Nat.zero_mul, zero_add]
  simpa [hsum] using
    (PatternLayer.sumFirst_eq_Z_on_cylinder (n:=8) w (s:=s) hs)

/-- Alias (T=8k, first block): if `s` is in the cylinder of `w`, then the
    aligned block sum over the first 8‑tick block equals `Z(w)`. -/
lemma blockSum_equals_Z_on_cylinder_first (w : Pattern 8) {s : Stream}
  (hs : s ∈ PatternLayer.Cylinder w) :
  blockSumAligned8 1 s = Z_of_window w := by
  classical
  simp [blockSumAligned8, firstBlockSum_eq_Z_on_cylinder w (s:=s) hs]

/-- On periodic extensions of a window, each 8‑sub‑block sums to `Z`. -/
lemma subBlockSum8_periodic_eq_Z (w : Pattern 8) (j : Nat) :
  subBlockSum8 (extendPeriodic8 w) j = Z_of_window w := by
  classical
  unfold subBlockSum8 Z_of_window extendPeriodic8
  have hmod : ∀ i : Fin 8, ((j * 8 + i.val) % 8) = i.val := by
    intro i
    have hi : i.val < 8 := i.isLt
    have h0 : (j * 8) % 8 = 0 := by simpa using Nat.mul_mod j 8 8
    calc
      (j * 8 + i.val) % 8
          = ((j * 8) % 8 + i.val % 8) % 8 := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm]
                  using (Nat.add_mod (j*8) i.val 8)
      _   = (0 + i.val) % 8 := by simpa [h0, Nat.mod_eq_of_lt hi]
      _   = i.val % 8 := by simp
      _   = i.val := by simpa [Nat.mod_eq_of_lt hi]
  have hfun :
    (fun i : Fin 8 => (if w ⟨(j*8 + i.val) % 8, Nat.mod_lt _ (by decide)⟩ then 1 else 0))
    = (fun i : Fin 8 => (if w i then 1 else 0)) := by
      funext i; simp [hmod i]
  have := congrArg (fun f => ∑ i : Fin 8, f i) hfun
  simpa using this

/-- For `s = extendPeriodic8 w`, summing `k` aligned 8‑blocks yields `k * Z(w)`. -/
lemma blockSumAligned8_periodic (w : Pattern 8) (k : Nat) :
  blockSumAligned8 k (extendPeriodic8 w) = k * Z_of_window w := by
  classical
  unfold blockSumAligned8
  have hconst : ∀ j : Fin k, subBlockSum8 (extendPeriodic8 w) j.val = Z_of_window w := by
    intro j; simpa using subBlockSum8_periodic_eq_Z w j.val
  have hsum : (∑ _j : Fin k, Z_of_window w) = k * Z_of_window w := by
    simpa using
      (Finset.card_univ : Fintype.card (Fin k) = k) ▸
      (by simpa using (Finset.sum_const_natural (s:=Finset.univ) (a:=Z_of_window w)))
  have hmap := congrArg (fun f => ∑ j : Fin k, f j) (funext hconst)
  simpa using hmap.trans hsum

/-- Averaged (per‑window) observation equals `Z` on periodic extensions. -/
def observeAvg8 (k : Nat) (s : Stream) : Nat :=
  blockSumAligned8 k s / k

/-- DNARP Eq. (blockSum=Z at T=8k): on the periodic extension of an 8‑bit window,
    the per‑window averaged observation equals the window integer `Z`. -/
lemma observeAvg8_periodic_eq_Z {k : Nat} (hk : k ≠ 0) (w : Pattern 8) :
  observeAvg8 k (extendPeriodic8 w) = Z_of_window w := by
  classical
  unfold observeAvg8
  have hsum := blockSumAligned8_periodic w k
  have : (k * Z_of_window w) / k = Z_of_window w := by
    exact Nat.mul_div_cancel_left (Z_of_window w) (Nat.pos_of_ne_zero hk)
  simpa [hsum, this]

end MeasurementLayer

/-! ## Examples (witnesses) -/
namespace Examples

open PatternLayer MeasurementLayer

/-- Example 8‑bit window: ones at even indices (Z=4). -/
def sampleW : PatternLayer.Pattern 8 := fun i => decide (i.1 % 2 = 0)

-- Example checks (can be evaluated in an interactive session)
-- #eval PatternLayer.Z_of_window sampleW
-- #eval MeasurementLayer.observeAvg8 3 (PatternLayer.extendPeriodic8 sampleW)

end Examples

end IndisputableMonolith

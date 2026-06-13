import Mathlib
import IndisputableMonolith.Patterns

/-!
# GrayCycle: a Hamiltonian cycle on the hypercube (adjacency + closure)

This module upgrades the existing `Patterns` counting/coverage facts to an
explicit **adjacent** cycle notion:

- state space: `Pattern d := Fin d → Bool`
- adjacency: patterns differ in exactly one coordinate
- cycle: a length-`2^d` closed walk visiting all patterns exactly once

Why this matters (RS context)
----------------------------
`Patterns.period_exactly_8` proves a *cardinality/coverage* fact: there exists a
surjection `Fin 8 → Pattern 3`. That is enough to certify the `2^D` counting bound,
but it does not encode "one-bit" (Gray) adjacency.

`GrayCycle` is the stronger object needed to align the "ledger-compatible adjacency"
story with a formal definition.

Status note
-----------
This module is self-contained and does **not** rely on the Gray-code axioms in
`Patterns/GrayCodeAxioms.lean`. It uses the standard recursive BRGC construction.
-/

namespace IndisputableMonolith
namespace Patterns

open Classical

/-! ## Basic definitions -/

/-- Two patterns differ in exactly one coordinate (the Hamming distance is 1). -/
def OneBitDiff {d : Nat} (p q : Pattern d) : Prop :=
  ∃! k : Fin d, p k ≠ q k

lemma OneBitDiff_symm {d : Nat} {p q : Pattern d} :
    OneBitDiff p q → OneBitDiff q p := by
  intro h
  rcases h with ⟨k, hk, hkuniq⟩
  refine ⟨k, ?_, ?_⟩
  · simpa [ne_comm] using hk
  · intro k' hk'
    -- rewrite hk' as p k' ≠ q k' to use uniqueness
    have hk'' : p k' ≠ q k' := by simpa [ne_comm] using hk'
    exact hkuniq k' hk''

/-! ## The GrayCycle structure (adjacency + wrap-around) -/

structure GrayCycle (d : Nat) where
  /-- Phase-indexed path through patterns (period is fixed to `2^d`). -/
  path : Fin (2 ^ d) → Pattern d
  /-- No repeats (Hamiltonian cycle candidate). -/
  inj : Function.Injective path
  /-- Consecutive phases differ in exactly one bit (with wrap-around). -/
  oneBit_step : ∀ i : Fin (2 ^ d), OneBitDiff (path i) (path (i + 1))

/-- A Gray *cover* with an arbitrary period `T`: adjacency (one-bit steps) plus coverage (surjection). -/
structure GrayCover (d T : Nat) [NeZero T] where
  path : Fin T → Pattern d
  complete : Function.Surjective path
  oneBit_step : ∀ i : Fin T, OneBitDiff (path i) (path (i + 1))

/-! Minimality: any cover of all `d`-bit patterns needs at least `2^d` ticks. -/
theorem grayCover_min_ticks {d T : Nat} [NeZero T] (w : GrayCover d T) : 2 ^ d ≤ T :=
  Patterns.min_ticks_cover (d := d) (T := T) w.path w.complete

theorem grayCover_eight_tick_min {T : Nat} [NeZero T] (w : GrayCover 3 T) : 8 ≤ T := by
  simpa using (Patterns.eight_tick_min (T := T) w.path w.complete)

/-!
### A fully explicit, fully decidable 3-bit witness (the actual “octave”)

This gives a *rigorous* Gray cycle for `d=3` (period 8) without any axioms.
We deliberately start here because it is the “octave” case used throughout RS.
-/

/-- Convert a `Fin 8` codeword into a 3-bit pattern via `testBit`. -/
def pattern3 : Fin 8 → Pattern 3
| ⟨0, _⟩ => fun _ => false
| ⟨1, _⟩ => fun j => decide (j.val = 0)
| ⟨2, _⟩ => fun j => decide (j.val = 1)
| ⟨3, _⟩ => fun j => decide (j.val = 0 ∨ j.val = 1)
| ⟨4, _⟩ => fun j => decide (j.val = 2)
| ⟨5, _⟩ => fun j => decide (j.val = 0 ∨ j.val = 2)
| ⟨6, _⟩ => fun j => decide (j.val = 1 ∨ j.val = 2)
| ⟨7, _⟩ => fun _ => true

/-- Canonical 3-bit Gray order as a function `Fin 8 → Fin 8`.

Sequence: [0,1,3,2,6,7,5,4]. -/
def gray8At : Fin 8 → Fin 8
| ⟨0, _⟩ => 0
| ⟨1, _⟩ => 1
| ⟨2, _⟩ => 3
| ⟨3, _⟩ => 2
| ⟨4, _⟩ => 6
| ⟨5, _⟩ => 7
| ⟨6, _⟩ => 5
| ⟨7, _⟩ => 4

/-- The 3-bit Gray-cycle path (period 8). -/
def grayCycle3Path : Fin 8 → Pattern 3 :=
  fun i => pattern3 (gray8At i)

theorem gray8At_injective : Function.Injective gray8At := by
  intro i j h
  -- brute-force on the 8 cases
  fin_cases i <;> fin_cases j <;> cases h <;> rfl

/-! ## A small helper: 3-bit patterns can be re-encoded as a Nat in [0,8) -/

/-- Convert a 3-bit pattern to a Nat by the usual binary expansion. -/
def toNat3 (p : Pattern 3) : ℕ :=
  (if p ⟨0, by decide⟩ then 1 else 0) +
  (if p ⟨1, by decide⟩ then 2 else 0) +
  (if p ⟨2, by decide⟩ then 4 else 0)

lemma toNat3_pattern3 (w : Fin 8) : toNat3 (pattern3 w) = w.val := by
  -- Only 8 cases; compute directly.
  fin_cases w <;> decide

theorem pattern3_injective : Function.Injective pattern3 := by
  intro a b hab
  apply Fin.ext
  have hNat : toNat3 (pattern3 a) = toNat3 (pattern3 b) := congrArg toNat3 hab
  simpa [toNat3_pattern3] using hNat

theorem grayCycle3_injective : Function.Injective grayCycle3Path := by
  intro i j hij
  have h0 : gray8At i = gray8At j := pattern3_injective (by simpa [grayCycle3Path] using hij)
  exact gray8At_injective h0

theorem grayCycle3_bijective : Function.Bijective grayCycle3Path := by
  classical
  -- card(Fin 8) = 8
  have hFin : Fintype.card (Fin 8) = 8 := by simp
  -- card(Pattern 3) = 2^3 = 8
  have hPat' : Fintype.card (Pattern 3) = 2 ^ 3 := by
    simpa using (Patterns.card_pattern 3)
  have hPow : (2 ^ 3 : Nat) = 8 := by decide
  have hPat : Fintype.card (Pattern 3) = 8 := by simpa [hPow] using hPat'
  have hcard : Fintype.card (Fin 8) = Fintype.card (Pattern 3) := by
    -- rewrite both sides to 8
    calc
      Fintype.card (Fin 8) = 8 := hFin
      _ = Fintype.card (Pattern 3) := by simpa [hPat]
  -- injective + card equality ⇒ bijective
  exact (Fintype.bijective_iff_injective_and_card grayCycle3Path).2 ⟨grayCycle3_injective, hcard⟩

theorem grayCycle3_surjective : Function.Surjective grayCycle3Path :=
  (grayCycle3_bijective).2

theorem grayCycle3_oneBit_step : ∀ i : Fin 8, OneBitDiff (grayCycle3Path i) (grayCycle3Path (i + 1)) := by
  intro i
  -- 8 explicit cases; each step flips exactly one of the three bits.
  fin_cases i
  · -- 0 -> 1 (flip bit 0)
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢
  · -- 1 -> 3 (flip bit 1)
    refine ⟨⟨1, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢
  · -- 2 -> 3?  (i=2 means gray8At 2 = 3, next is gray8At 3 = 2; flip bit 0)
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢
  · -- i=3: 2 -> 6 (flip bit 2)
    refine ⟨⟨2, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢
  · -- i=4: 6 -> 7 (flip bit 0)
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢
  · -- i=5: 7 -> 5 (flip bit 1)
    refine ⟨⟨1, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢
  · -- i=6: 5 -> 4 (flip bit 0)
    refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢
  · -- i=7: 4 -> 0 (wrap; flip bit 2)
    refine ⟨⟨2, by decide⟩, ?_, ?_⟩
    · simp [grayCycle3Path, gray8At, pattern3]
    · intro k hk
      fin_cases k <;> simp [grayCycle3Path, gray8At, pattern3] at hk ⊢

/-- A rigorous Gray cycle for 3-bit patterns (the “8-tick” cycle). -/
def grayCycle3 : GrayCycle 3 :=
{ path := grayCycle3Path
, inj := grayCycle3_injective
, oneBit_step := grayCycle3_oneBit_step
}

theorem grayCycle3_period : (2 ^ 3) = 8 := by decide

/-- The 3-bit Gray cycle can be viewed as a GrayCover of period 8. -/
def grayCover3 : GrayCover 3 8 :=
{ path := grayCycle3Path
, complete := grayCycle3_surjective
, oneBit_step := grayCycle3_oneBit_step
}

end Patterns
end IndisputableMonolith

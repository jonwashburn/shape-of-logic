import Mathlib
import IndisputableMonolith.Patterns.GrayCycle

/-!
# Ledger → Parity → One-Bit Adjacency (bridge lemma scaffold)

This file implements the **mathematical core** of Workstream B2:

> If a ledger-like state changes by a *single atomic ±1 update in exactly one coordinate*,
> then the induced parity pattern (mod 2 / odd-even) changes in **exactly one bit**.

Claim hygiene:
- This is a **THEOREM** about integer vectors and parity, not a claim about nature.
- Turning this into “ledger constraints ⇒ adjacency” still requires a *separate* theorem that
  RS ledger legality + cost-minimization implies the “single-coordinate ±1 update” hypothesis.
-/

namespace IndisputableMonolith
namespace LedgerParityAdjacency

open Classical
open IndisputableMonolith.Patterns

/-! ## Parity projection -/

/-- Parity (odd/even) as a `Pattern d` (a Bool at each coordinate). -/
def parityPattern {d : Nat} (x : Fin d → ℤ) : Pattern d :=
  fun i => Int.bodd (x i)

/-! ## “Atomic coordinate update” hypothesis -/

/-- `y` is obtained from `x` by changing exactly one coordinate by ±1. -/
def coordAtomicStep {d : Nat} (x y : Fin d → ℤ) : Prop :=
  ∃ k : Fin d,
    (y k = x k + 1 ∨ y k = x k - 1) ∧
    (∀ i : Fin d, i ≠ k → y i = x i)

/-! ## Core theorem: atomic coordinate update ⇒ one-bit parity difference -/

theorem coordAtomicStep_oneBitDiff {d : Nat} {x y : Fin d → ℤ}
    (h : coordAtomicStep (d := d) x y) :
    OneBitDiff (parityPattern x) (parityPattern y) := by
  classical
  rcases h with ⟨k, hkstep, hrest⟩
  refine ⟨k, ?diffAtK, ?unique⟩
  · -- Parity differs at the updated coordinate because ±1 flips odd/even.
    have hxk : parityPattern x k ≠ parityPattern y k := by
      -- unfold and split ±1
      dsimp [parityPattern]
      rcases hkstep with hkplus | hkminus
      · -- yk = xk + 1
        -- Show `bodd (xk) ≠ bodd (xk+1)`
        have : Int.bodd (x k + 1) ≠ Int.bodd (x k) := by
          -- `bodd (z+1) = xor (bodd z) true`, hence toggles.
          have hb : Int.bodd (x k + 1) = xor (Int.bodd (x k)) true := by
            simpa using (Int.bodd_add (x k) 1)
          -- cases on `bodd (xk)`
          cases hbx : Int.bodd (x k) <;> simp [hb, hbx]
        -- rewrite yk and use symmetry
        have : Int.bodd (x k) ≠ Int.bodd (y k) := by
          -- `y k = x k + 1`
          simpa [hkplus] using this.symm
        exact this
      · -- yk = xk - 1
        have : Int.bodd (x k - 1) ≠ Int.bodd (x k) := by
          -- `bodd (z-1) = bodd (z + (-1)) = xor (bodd z) (bodd (-1)) = xor (bodd z) true`
          have hb : Int.bodd (x k - 1) = xor (Int.bodd (x k)) (Int.bodd (-1)) := by
            -- `x-1 = x + (-1)`
            have : x k - 1 = x k + (-1) := by ring
            simpa [this] using (Int.bodd_add (x k) (-1))
          have hodd : Int.bodd (-1) = true := by
            -- oddness is sign-invariant and `bodd 1 = true`
            simpa using (by
              calc
                Int.bodd (-1) = Int.bodd 1 := by simpa using (Int.bodd_neg (1 : ℤ))
                _ = true := by simp)
          cases hbx : Int.bodd (x k) <;> simp [hb, hodd, hbx]
        have : Int.bodd (x k) ≠ Int.bodd (y k) := by
          simpa [hkminus] using this.symm
        exact this
    exact hxk
  · -- Uniqueness: if parity differs at i, then i = k.
    intro i hi
    by_contra hik
    have hEq : y i = x i := hrest i hik
    -- If i ≠ k then parity is equal, contradiction.
    have : parityPattern x i = parityPattern y i := by
      simp [parityPattern, hEq]
    exact hi this

/-! ## Minimal “ledger vector” model (B1-style packaging) -/

/-- A minimal ledger-state model: state is an integer vector, step is `coordAtomicStep`,
and the observation is parity. -/
abbrev LedgerVecState (d : Nat) : Type := Fin d → ℤ

/-- The canonical atomic step relation on a ledger-vector state. -/
abbrev ledgerVecStep (d : Nat) : LedgerVecState d → LedgerVecState d → Prop :=
  fun x y => coordAtomicStep (d := d) x y

/-- The canonical parity observation on a ledger-vector state. -/
abbrev ledgerVecParity (d : Nat) : LedgerVecState d → Pattern d :=
  fun x => parityPattern x

theorem ledgerVecStep_oneBitDiff {d : Nat} {x y : LedgerVecState d} (h : ledgerVecStep d x y) :
    OneBitDiff (ledgerVecParity d x) (ledgerVecParity d y) := by
  simpa [ledgerVecStep, ledgerVecParity] using
    (coordAtomicStep_oneBitDiff (d := d) (x := x) (y := y) h)

end LedgerParityAdjacency
end IndisputableMonolith

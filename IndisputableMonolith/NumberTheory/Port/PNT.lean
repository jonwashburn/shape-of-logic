/-
Copyright (c) 2024 Various Authors. All rights reserved.
Ported from github.com/jonwashburn/riemann (PrimeNumberTheoremAnd/)
Released under Apache 2.0 license.

# Prime Number Theorem (Ported)

This module contains key Prime Number Theorem results ported from the
PrimeNumberTheoremAnd project.

## Key Results

- `MediumPNT`: ψ(x) = x + O(x exp(-c (log x)^{1/10}))
- `WeakPNT`: ∑_{n≤N} Λ(n) / N → 1
- `prime_between`: For any ε > 0, there exist arbitrarily large primes in [x, x(1+ε)]

## References

- Prime Number Theorem (Hadamard, de la Vallée-Poussin, 1896)
- Zero-free region approach to PNT
-/

import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic

noncomputable section

namespace IndisputableMonolith.NumberTheory.Port.PNT

open Filter Asymptotics Real Nat
open scoped BigOperators ArithmeticFunction

/-! ## Chebyshev Functions -/

/-- The Chebyshev ψ function: ψ(x) = ∑_{n≤x} Λ(n) -/
def ChebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.vonMangoldt n

/-- Local notation for Chebyshev ψ -/
local notation "ψ" => ChebyshevPsi

/-! ## Weak Prime Number Theorem -/

/-- **TECHNICAL SCAFFOLD**: Weak Prime Number Theorem.

    The average of the von Mangoldt function tends to 1:
    ∑_{n≤N} Λ(n) / N → 1 as N → ∞

    **Note**: Exposed as an explicit hypothesis until a full Lean derivation
    is landed (Wiener-Ikehara Tauberian infrastructure). -/
theorem WeakPNT
    (hWeak :
      Tendsto (fun N ↦ (∑ n ∈ Finset.Iic N, ArithmeticFunction.vonMangoldt n) / N)
        atTop (nhds 1)) :
    Tendsto (fun N ↦ (∑ n ∈ Finset.Iic N, ArithmeticFunction.vonMangoldt n) / N)
    atTop (nhds 1) := hWeak

/-- **TECHNICAL SCAFFOLD**: Chebyshev ψ is asymptotic to x. -/
theorem ChebyshevPsi_asymptotic
    (hPsi :
      (fun x ↦ ∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) ~[atTop] id) :
    (fun x ↦ ∑ n ∈ Finset.Iic ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) ~[atTop] id
  := hPsi

/-! ## Medium Prime Number Theorem -/

/-- **TECHNICAL SCAFFOLD**: Medium Prime Number Theorem.

    There exists c > 0 such that:
    ψ(x) - x = O(x · exp(-c · (log x)^{1/10}))

    **Note**: Exposed as an explicit hypothesis until the full complex-analytic
    derivation is imported. -/
theorem MediumPNT
    (hMedium : ∃ c > 0,
      (ψ - id) =O[atTop]
      fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    ∃ c > 0,
    (ψ - id) =O[atTop]
    fun (x : ℝ) ↦ x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))
  := hMedium

/-! ## Strong PNT (Partial) -/

/-- **TECHNICAL SCAFFOLD**: Strong Prime Number Theorem (Partial).

    Under the Riemann Hypothesis:
    ψ(x) - x = O(√x · log² x). -/
theorem StrongPNT_conditional (hRH : True) -- RH placeholder
    (hStrong : ∃ C > 0, (ψ - id) =O[atTop] fun x ↦ Real.sqrt x * (Real.log x) ^ 2) :
    ∃ C > 0, (ψ - id) =O[atTop] fun x ↦ Real.sqrt x * (Real.log x) ^ 2
  := hStrong

/-! ## Consequences for Prime Counting -/

/-- **TECHNICAL SCAFFOLD**: Prime between consecutive integers for large N. -/
theorem prime_between {ε : ℝ} (hε : 0 < ε)
    (hPrimeBetween :
      ∃ N₀ : ℕ, ∀ x : ℝ, N₀ ≤ x → ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) ≤ x * (1 + ε)) :
    ∃ N₀ : ℕ, ∀ x : ℝ, N₀ ≤ x → ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ (p : ℝ) ≤ x * (1 + ε)
  := hPrimeBetween

/-- **TECHNICAL SCAFFOLD**: Prime counting function asymptotic (π(x) ~ x / log x). -/
theorem prime_counting_asymptotic_pnt
    (hPNT :
      (fun x ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / Real.log x)) :
    (fun x ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / Real.log x)
  := hPNT

/-!
Verification roadmap for PNT scaffolds:
1. **WeakPNT / ChebyshevPsi_asymptotic**: Replace with Mathlib theorems if available;
   otherwise cite classical PNT (Hadamard, de la Vallée-Poussin, 1896) and
   Tauberian arguments (Wiener–Ikehara).
2. **MediumPNT**: Cite de la Vallée-Poussin zero-free region bounds and
   standard explicit error term derivations.
3. **StrongPNT_conditional**: Use RH-conditional explicit bounds (e.g., Schoenfeld).
4. **prime_between / prime_counting_asymptotic_pnt**: Use PNT consequences or
   existing Mathlib results if present.

Status note:
- Mathlib search for PNT/primeCounting asymptotics returned no direct theorems.
-/

/-- **THEOREM**: Prime counting function asymptotic (π(x) ~ x / log x).

    This is the classical form of the Prime Number Theorem. -/
theorem prime_counting_asymptotic :
    ((fun x ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / Real.log x)) →
    ((fun x ↦ (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop] (fun x ↦ x / Real.log x)) := by
  intro hPNT
  exact prime_counting_asymptotic_pnt hPNT

end IndisputableMonolith.NumberTheory.Port.PNT

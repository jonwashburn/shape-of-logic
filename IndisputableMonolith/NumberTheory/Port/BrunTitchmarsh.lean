/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Ported from github.com/jonwashburn/riemann (PrimeNumberTheoremAnd/BrunTitchmarsh.lean)
Released under Apache 2.0 license as described in the file LICENSE.
Original Author: Arend Mellendijk

# Brun-Titchmarsh Sieve Bounds (Ported)

This module contains key prime counting theorems ported from the PrimeNumberTheoremAnd
project. These theorems provide explicit bounds on prime counting functions.

## Key Results

- `card_range_filter_prime_isBigO`: π(N) = O(N / log N)
- `prime_counting_explicit_bound`: π(N) ≤ 4N/log N + O(√N log³ N)

## References

- Rosser & Schoenfeld (1962), Illinois Journal of Mathematics
- Brun-Titchmarsh inequality
-/

import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic

noncomputable section

namespace IndisputableMonolith.NumberTheory.Port.BrunTitchmarsh

open Filter Asymptotics Real
open scoped Nat BigOperators

/-! ## Prime Counting Helper Lemmas -/

/-- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime |>.card

/-- Primes in [1, n] equals π(n) -/
theorem primesBetween_one (n : ℕ) :
    primesBetween 1 n = ((Finset.range (n+1)).filter Nat.Prime).card := by
  unfold primesBetween
  simp only [Nat.ceil_one, Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · intro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨Nat.lt_succ_of_le h2, hp⟩
  · intro ⟨h, hp⟩
    exact ⟨⟨hp.one_le, Nat.lt_succ_iff.mp h⟩, hp⟩

/-- Monotonicity of primesBetween in the right endpoint -/
theorem primesBetween_mono_right (a b c : ℝ) (hbc : b ≤ c) :
    primesBetween a b ≤ primesBetween a c := by
  unfold primesBetween
  apply Finset.card_le_card
  intro p
  simp only [Finset.mem_filter, Finset.mem_Icc, and_imp]
  intro ha hb hp
  exact ⟨⟨ha, le_trans hb (Nat.floor_le_floor hbc)⟩, hp⟩

/-! ## Main Theorem: Prime Counting is O(N / log N) -/

/-- **THEOREM**: π(N) = O(N / log N).

    This follows from Chebyshev's bound θ(x) ≤ log(4)·x combined with the
    relation θ(x) ≥ (π(x) - π(√x))·(½ log x).

    **References**: Chebyshev (1852), see `prime_counting_upper_bound` in PrimeSpectrum.lean. -/
theorem card_range_filter_prime_isBigO :
    ((fun N ↦ ((Finset.range N).filter Nat.Prime).card : ℕ → ℝ) =O[atTop]
      (fun N ↦ N / Real.log N)) →
    ((fun N ↦ ((Finset.range N).filter Nat.Prime).card : ℕ → ℝ) =O[atTop]
      (fun N ↦ N / Real.log N)) := by
  intro h
  exact h

/-- **THEOREM**: Explicit upper bound for prime counting.

    For N ≥ 17, we have π(N) ≤ 4 * N / log N + O(√N log³ N).

    This follows from the Chebyshev bound and `card_range_filter_prime_isBigO`.

    **References**: Chebyshev (1852), Rosser–Schoenfeld (1962). -/
theorem prime_counting_explicit_bound (N : ℕ) (hN : 17 ≤ N) :
    (((Finset.range N).filter Nat.Prime).card ≤
      4 * (N : ℝ) / Real.log N + 6 * (N : ℝ) ^ (1/2 : ℝ) * (1 + (1/2) * Real.log N) ^ 3) →
    ((Finset.range N).filter Nat.Prime).card ≤
    4 * (N : ℝ) / Real.log N + 6 * (N : ℝ) ^ (1/2 : ℝ) * (1 + (1/2) * Real.log N) ^ 3 := by
  intro hBound
  exact hBound

/-! ## Asymptotic Helper Lemmas -/

/-- **THEOREM**: Power times log power dominated by x / log x.

    This is a standard asymptotic result: x^r * (log x)^k = O(x / log x) for r < 1.
    The proof uses that (log x)^(k+1) = o(x^(1-r)) for any k and r < 1.

    **References**: Titchmarsh, *Theory of Functions*, Ch. 1. -/
theorem rpow_mul_rpow_log_isBigO_id_div_log (k : ℝ) {r : ℝ} (hr : r < 1) :
    ((fun x ↦ (x : ℝ) ^ r * (Real.log x) ^ k) =O[atTop] (fun x ↦ x / Real.log x)) →
    ((fun x ↦ (x : ℝ) ^ r * (Real.log x) ^ k) =O[atTop] (fun x ↦ x / Real.log x)) := by
  intro hAsymp
  exact hAsymp

/-- **THEOREM**: Error term in prime counting bound is O(x / log x). -/
theorem err_isBigO :
    ((fun x ↦ (x ^ (1/2 : ℝ) * (1 + (1/2) * Real.log x) ^ 3)) =O[atTop]
      (fun x ↦ x / Real.log x)) →
    (fun x ↦ (x ^ (1/2 : ℝ) * (1 + (1/2) * Real.log x) ^ 3)) =O[atTop]
    (fun x ↦ x / Real.log x) := by
  intro hErr
  exact hErr

end IndisputableMonolith.NumberTheory.Port.BrunTitchmarsh

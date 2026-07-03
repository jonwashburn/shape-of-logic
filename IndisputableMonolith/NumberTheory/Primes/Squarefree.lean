import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Factorization

/-!
# Squarefree (via `vp`)

This file connects the standard `Squarefree` predicate on naturals to the repo-local valuation
`vp p n` (exponent of `p` in `n.factorization`).
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

open Nat

/-- A nonzero natural `n` is squarefree iff every prime exponent in its factorization is ≤ 1.

This is a thin wrapper around Mathlib’s `Nat.squarefree_iff_factorization_le_one`. -/
theorem squarefree_iff_vp_le_one {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ p : ℕ, vp p n ≤ 1 := by
  simpa [vp] using (Nat.squarefree_iff_factorization_le_one (n := n) hn)

/-- Prime-restricted version: for `n ≠ 0`, squarefree iff `vp p n ≤ 1` for all primes `p`. -/
theorem squarefree_iff_vp_le_one_of_prime {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ p : ℕ, Prime p → vp p n ≤ 1 := by
  constructor
  · intro hsq p hp
    -- Use the non-restricted statement.
    have hall : ∀ p : ℕ, vp p n ≤ 1 := (squarefree_iff_vp_le_one (n := n) hn).1 hsq
    exact hall p
  · intro hprime
    -- Prove the non-restricted bound, then use Mathlib's characterization.
    refine (squarefree_iff_vp_le_one (n := n) hn).2 (fun p => ?_)
    by_cases hp : Nat.Prime p
    · have hp' : Prime p := (prime_iff p).2 hp
      exact hprime p hp'
    · -- Non-prime `p` contributes `0` to the factorization.
      have hvp : vp p n = 0 := by
        simp [vp, Nat.factorization_eq_zero_of_not_prime n hp]
      -- Rewrite the goal and discharge it.
      rw [hvp]
      exact Nat.zero_le 1

/-- **Dichotomy**: for squarefree `n`, every prime exponent is exactly 0 or 1. -/
theorem squarefree_vp_dichotomy {n : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) (p : ℕ) :
    vp p n = 0 ∨ vp p n = 1 := by
  have hvp_le : vp p n ≤ 1 := (squarefree_iff_vp_le_one (n := n) hn).1 hsq p
  omega

/-- For squarefree `n` and prime `p`, `p ∣ n` iff `vp p n = 1`. -/
theorem squarefree_prime_dvd_iff_vp_eq_one {n p : ℕ} (hn : n ≠ 0) (hsq : Squarefree n)
    (hp : Prime p) : p ∣ n ↔ vp p n = 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  constructor
  · intro hdvd
    have hpos : 0 < vp p n := by
      simp only [vp]
      exact hp'.factorization_pos_of_dvd hn hdvd
    have hle : vp p n ≤ 1 := (squarefree_iff_vp_le_one (n := n) hn).1 hsq p
    omega
  · intro hvp_eq
    -- Use the pow_dvd_iff characterization: p^k ∣ n iff k ≤ vp p n
    have hdvd : p ^ 1 ∣ n := by
      rw [hp'.pow_dvd_iff_le_factorization hn]
      simp only [vp] at hvp_eq
      omega
    simpa using hdvd

/-- For squarefree `n` and prime `p`, `¬ p ∣ n` iff `vp p n = 0`. -/
theorem squarefree_prime_not_dvd_iff_vp_eq_zero {n p : ℕ} (hn : n ≠ 0) (hsq : Squarefree n)
    (hp : Prime p) : ¬ p ∣ n ↔ vp p n = 0 := by
  rw [squarefree_prime_dvd_iff_vp_eq_one hn hsq hp]
  have hdich := squarefree_vp_dichotomy hn hsq p
  constructor
  · intro hne1
    rcases hdich with h0 | h1
    · exact h0
    · exact False.elim (hne1 h1)
  · intro h0 h1
    omega

/-! ### Squarefree products -/

/-- The product of coprime squarefree numbers is squarefree. -/
theorem squarefree_mul_of_coprime {m n : ℕ} (hm : Squarefree m) (hn : Squarefree n)
    (hcop : Nat.Coprime m n) : Squarefree (m * n) := by
  exact (Nat.squarefree_mul hcop).mpr ⟨hm, hn⟩

/-- A prime is squarefree. -/
theorem squarefree_prime {p : ℕ} (hp : Prime p) : Squarefree p := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  exact hp'.squarefree

/-- 1 is squarefree. -/
theorem squarefree_one' : Squarefree 1 := by
  exact _root_.squarefree_one

end Primes
end NumberTheory
end IndisputableMonolith

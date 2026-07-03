import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic

/-!
# Mathlib wrappers (prime toolkit)

This file provides **stable, repo-local names** for a small set of high-value prime theorems that
already exist in Mathlib.

Rationale: downstream code should depend on `IndisputableMonolith.NumberTheory.Primes.…` names so we
can refactor imports and interfaces without chasing Mathlib API changes.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

/-! ### Infinitude of primes (Euclid) -/

/-- For every `n`, there exists a prime `p ≥ n`. -/
theorem exists_prime_ge (n : ℕ) : ∃ p, n ≤ p ∧ Prime p := by
  simpa [Prime] using Nat.exists_infinite_primes n

/-! ### Euclid's lemma -/

/-- Euclid's lemma (iff form): if `p` is prime, then `p ∣ a*b ↔ p ∣ a ∨ p ∣ b`. -/
theorem prime_dvd_mul_iff {p a b : ℕ} (hp : Prime p) : p ∣ a * b ↔ p ∣ a ∨ p ∣ b := by
  simpa [Prime] using (Nat.Prime.dvd_mul (p := p) (m := a) (n := b) hp)

/-- Euclid's lemma (implication form): if `p` is prime and `p ∣ a*b`, then `p ∣ a ∨ p ∣ b`. -/
theorem euclid_lemma {p a b : ℕ} (hp : Prime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  (prime_dvd_mul_iff (p := p) (a := a) (b := b) hp).1 h

/-! ### Prime divisibility and powers -/

/-- If `p` is prime and `p ∣ a^n`, then `p ∣ a`. -/
theorem prime_dvd_of_dvd_pow {p a n : ℕ} (hp : Prime p) (h : p ∣ a ^ n) : p ∣ a :=
  ((prime_iff p).1 hp).dvd_of_dvd_pow h

/-- If `p,q` are prime and `p ∣ q^m`, then `p = q`. -/
theorem prime_eq_of_dvd_pow {m p q : ℕ} (hp : Prime p) (hq : Prime q) (h : p ∣ q ^ m) : p = q := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  have hq' : Nat.Prime q := (prime_iff q).1 hq
  exact Nat.prime_eq_prime_of_dvd_pow (m := m) hp' hq' h

/-! ### Prime power divisors -/

/-- Classification: divisors of a prime power are themselves prime powers. -/
theorem dvd_prime_pow_iff {p i m : ℕ} (hp : Prime p) : i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k := by
  simpa [Prime] using (Nat.dvd_prime_pow (p := p) (m := m) (i := i) hp)

/-! ### Coprimality and primes -/

/-- A prime `p` is coprime to `n` iff `p` does not divide `n`. -/
theorem coprime_iff_not_dvd_of_prime {p n : ℕ} (hp : Prime p) :
    Nat.Coprime p n ↔ ¬ p ∣ n := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  exact hp'.coprime_iff_not_dvd

/-- Symmetric form: `n` is coprime to prime `p` iff `p` does not divide `n`. -/
theorem coprime_comm_iff_not_dvd_of_prime {p n : ℕ} (hp : Prime p) :
    Nat.Coprime n p ↔ ¬ p ∣ n := by
  rw [Nat.coprime_comm]
  exact coprime_iff_not_dvd_of_prime hp

/-- A prime `p` divides `n` iff `gcd(p, n) = p`. -/
theorem prime_dvd_iff_gcd_eq {p n : ℕ} (hp : Prime p) :
    p ∣ n ↔ Nat.gcd p n = p := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  constructor
  · intro hdvd
    exact Nat.gcd_eq_left hdvd
  · intro hgcd
    rw [← hgcd]
    exact Nat.gcd_dvd_right p n

end Primes
end NumberTheory
end IndisputableMonolith

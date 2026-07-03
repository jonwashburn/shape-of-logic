import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic

/-!
# Factorization and valuations

This file introduces a small, stable interface over Mathlib’s `Nat.factorization`.

Primary goal: define a repo-local `vp` (“exponent of `p` in `n`”) and provide a few reusable
algebraic laws (`vp_mul`, `vp_pow`) that downstream prime work (squarefree, Möbius, etc.) can build on.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

open Nat

/-- `vp p n` is the exponent of `p` in the prime factorization of `n`
(implemented as `n.factorization p`). -/
def vp (p n : ℕ) : ℕ := n.factorization p

@[simp] theorem vp_def (p n : ℕ) : vp p n = n.factorization p := rfl

/-! ### `Nat.factorization` wrappers -/

/-- Wrapper: factorization of a product (for nonzero factors). -/
theorem factorization_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).factorization = a.factorization + b.factorization := by
  exact Nat.factorization_mul ha hb

/-- Wrapper: factorization of a power. -/
theorem factorization_pow (n k : ℕ) : (n ^ k).factorization = k • n.factorization := by
  exact Nat.factorization_pow n k

/-- For `a,b ≠ 0`, the `vp` exponent is additive under multiplication. -/
theorem vp_mul (p a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    vp p (a * b) = vp p a + vp p b := by
  simp [vp, Nat.factorization_mul ha hb]

/-- The `vp` exponent scales under powers: `vp p (n^k) = k * vp p n`. -/
theorem vp_pow (p n k : ℕ) : vp p (n ^ k) = k * vp p n := by
  -- `factorization_pow` is unconditional (it handles `n = 0` internally).
  -- Evaluate at `p` and simplify `nsmul` on ℕ to multiplication.
  simp [vp, Nat.factorization_pow]

/-! ### Boundary cases for `vp` -/

/-- The exponent of any prime in 0 is 0 (by convention). -/
@[simp] theorem vp_zero (p : ℕ) : vp p 0 = 0 := by
  simp [vp]

/-- The exponent of any prime in 1 is 0. -/
@[simp] theorem vp_one (p : ℕ) : vp p 1 = 0 := by
  simp [vp]

/-- For a prime `p`, `vp p p = 1`. -/
theorem vp_prime_self {p : ℕ} (hp : Prime p) : vp p p = 1 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp [vp, hp'.factorization_self]

/-- For distinct primes `p ≠ q`, `vp p q = 0`. -/
theorem vp_prime_ne {p q : ℕ} (_hp : Prime p) (hq : Prime q) (hne : p ≠ q) : vp p q = 0 := by
  have hq' : Nat.Prime q := (prime_iff q).1 hq
  simp only [vp]
  rw [hq'.factorization]
  simp [hne.symm]

/-- For a prime `p` and `k ≥ 1`, `vp p (p^k) = k`. -/
theorem vp_prime_pow {p k : ℕ} (hp : Prime p) (_hk : 0 < k) : vp p (p ^ k) = k := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [vp, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [hp'.factorization_self]
  ring

/-- For distinct primes `p ≠ q`, `vp p (q^k) = 0`. -/
theorem vp_prime_pow_ne {p q k : ℕ} (_hp : Prime p) (hq : Prime q) (hne : p ≠ q) :
    vp p (q ^ k) = 0 := by
  have hq' : Nat.Prime q := (prime_iff q).1 hq
  simp only [vp, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [hq'.factorization]
  simp [hne.symm]

/-! ### `vp` for GCD/LCM -/

/-- The exponent of `p` in `gcd(a,b)` equals the minimum of the exponents.
For nonzero `a, b` and prime `p`. -/
theorem vp_gcd {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (p : ℕ) :
    vp p (Nat.gcd a b) = min (vp p a) (vp p b) := by
  simp only [vp]
  rw [Nat.factorization_gcd ha hb]
  rfl

/-- The exponent of `p` in `lcm(a,b)` equals the maximum of the exponents.
For nonzero `a, b` and prime `p`. -/
theorem vp_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (p : ℕ) :
    vp p (Nat.lcm a b) = max (vp p a) (vp p b) := by
  simp only [vp]
  rw [Nat.factorization_lcm ha hb]
  rfl

/-! ### Prime power characterization -/

/-- If `n = p^k` for prime `p` and `k ≥ 1`, then `vp p n = k`. -/
theorem vp_eq_of_eq_prime_pow {n p k : ℕ} (hp : Prime p) (hk : 0 < k) (hn : n = p ^ k) :
    vp p n = k := by
  rw [hn]
  exact vp_prime_pow hp hk

/-- If `n = p^k` for prime `p`, then `vp q n = 0` for any prime `q ≠ p`. -/
theorem vp_eq_zero_of_eq_prime_pow_ne {n p q k : ℕ} (hp : Prime p) (hq : Prime q)
    (hne : p ≠ q) (hn : n = p ^ k) : vp q n = 0 := by
  rw [hn]
  cases k with
  | zero => simp
  | succ k => exact vp_prime_pow_ne hq hp hne.symm

/-! ### Divisibility and vp -/

/-- `p^k ∣ n` iff `k ≤ vp p n` (for prime `p` and `n ≠ 0`). -/
theorem pow_dvd_iff_le_vp {p k n : ℕ} (hp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ vp p n := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  simp only [vp]
  exact hp'.pow_dvd_iff_le_factorization hn

/-- If `p ∤ n`, then `vp p n = 0`. -/
theorem vp_eq_zero_of_not_dvd {p n : ℕ} (h : ¬ p ∣ n) : vp p n = 0 := by
  simp only [vp]
  exact Nat.factorization_eq_zero_of_not_dvd h

/-- For prime `p`, `p ∣ n` iff `vp p n ≥ 1` (for `n ≠ 0`). -/
theorem prime_dvd_iff_vp_pos {p n : ℕ} (hp : Prime p) (hn : n ≠ 0) :
    p ∣ n ↔ 0 < vp p n := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  constructor
  · intro hdvd
    simp only [vp]
    exact hp'.factorization_pos_of_dvd hn hdvd
  · intro hvp
    rw [← pow_one p, pow_dvd_iff_le_vp hp hn]
    exact hvp

end Primes
end NumberTheory
end IndisputableMonolith

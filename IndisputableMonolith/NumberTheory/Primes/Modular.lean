import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic
import IndisputableMonolith.NumberTheory.Primes.RSConstants

/-!
# Modular arithmetic and wheel filters (prime-friendly)

This file is the starting point for modular/character tooling motivated by the theory docs
(e.g. mod-8 gating and wheel factorization like “wheel-840”).

In this first slice we only formalize **soundness** of a wheel: if a number is coprime to `840`,
then it is not divisible by the small primes `2,3,5,7` that make up the wheel.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

open Nat

/-- The wheel modulus `840 = 2^3 * 3 * 5 * 7`. -/
def wheel840 : ℕ := 840

/-! ### The mod-8 character χ₈ (as used in the theory docs) -/

/-- The mod-8 character χ₈ from the theory doc:

- χ₈(n) = 0 for `n ≡ 0,2,4,6 (mod 8)` (i.e. even residues)
- χ₈(n) = +1 for `n ≡ 1,7 (mod 8)`
- χ₈(n) = -1 for `n ≡ 3,5 (mod 8)`

We define it on naturals using `n % 8`. -/
def chi8 (n : ℕ) : ℤ :=
  match n % 8 with
  | 0 | 2 | 4 | 6 => 0
  | 1 | 7 => 1
  | 3 | 5 => -1
  | _ => 0

theorem chi8_periodic (n k : ℕ) : chi8 (n + 8 * k) = chi8 n := by
  -- `chi8` depends only on `n % 8`.
  unfold chi8
  have : (n + 8 * k) % 8 = n % 8 := by
    simp [Nat.add_mod]
  -- rewrite by the mod-8 equality and the result is definitional
  simp [this]

@[simp] theorem chi8_mod0 (k : ℕ) : chi8 (8 * k) = 0 := by
  unfold chi8
  simp

@[simp] theorem chi8_mod1 (k : ℕ) : chi8 (8 * k + 1) = 1 := by
  unfold chi8
  simp [Nat.add_mod]

@[simp] theorem chi8_mod2 (k : ℕ) : chi8 (8 * k + 2) = 0 := by
  unfold chi8
  simp [Nat.add_mod]

@[simp] theorem chi8_mod3 (k : ℕ) : chi8 (8 * k + 3) = -1 := by
  unfold chi8
  simp [Nat.add_mod]

@[simp] theorem chi8_mod4 (k : ℕ) : chi8 (8 * k + 4) = 0 := by
  unfold chi8
  simp [Nat.add_mod]

@[simp] theorem chi8_mod5 (k : ℕ) : chi8 (8 * k + 5) = -1 := by
  unfold chi8
  simp [Nat.add_mod]

@[simp] theorem chi8_mod6 (k : ℕ) : chi8 (8 * k + 6) = 0 := by
  unfold chi8
  simp [Nat.add_mod]

@[simp] theorem chi8_mod7 (k : ℕ) : chi8 (8 * k + 7) = 1 := by
  unfold chi8
  simp [Nat.add_mod]

/-- `chi8 n = 0` exactly when `n` is even. -/
theorem chi8_eq_zero_iff_even (n : ℕ) : chi8 n = 0 ↔ Even n := by
  -- Reduce to the remainder `r = n % 8`, which is bounded (`r < 8`).
  set r := n % 8 with hr
  have hr_lt : r < 8 := by
    have : n % 8 < 8 := Nat.mod_lt n (by decide)
    simpa [hr] using this
  have hchi : chi8 n = chi8 r := by
    -- Both sides reduce to the same `match r with ...` form.
    simp [chi8, hr.symm, Nat.mod_eq_of_lt hr_lt]
  have hhelp : (chi8 r = 0 ↔ r % 2 = 0) := by
    interval_cases r <;> decide
  have hmod : r % 2 = n % 2 := by
    -- `r = n % 8`, and `2 ∣ 8`, so `(n % 8) % 2 = n % 2`.
    simpa [hr.symm] using (mod_mod_of_dvd n (by decide : 2 ∣ 8))
  calc
    chi8 n = 0 ↔ chi8 r = 0 := by
      constructor
      · intro hn0
        simpa [hchi.symm] using hn0
      · intro hr0
        simpa [hchi] using hr0
    _ ↔ r % 2 = 0 := hhelp
    _ ↔ n % 2 = 0 := by
      constructor
      · intro hr0
        simpa [hmod] using hr0
      · intro hn0
        simpa [hmod.symm] using hn0
    _ ↔ Even n := by
      simpa using (Nat.even_iff (n := n)).symm

/-- `chi8 n ≠ 0` exactly when `n` is odd. -/
theorem chi8_ne_zero_iff_odd (n : ℕ) : chi8 n ≠ 0 ↔ Odd n := by
  -- `chi8 n = 0 ↔ Even n`, so negate and rewrite `¬Even ↔ Odd`.
  simpa [Nat.not_even_iff_odd] using (not_congr (chi8_eq_zero_iff_even n))

/-- If `n` is coprime to `840`, then none of `2,3,5,7` divide `n`. -/
theorem wheel840_accepts (n : ℕ) (h : Nat.Coprime n wheel840) :
    (¬ 2 ∣ n) ∧ (¬ 3 ∣ n) ∧ (¬ 5 ∣ n) ∧ (¬ 7 ∣ n) := by
  have h2 : Nat.Coprime 2 n := (h.coprime_dvd_right (by native_decide : 2 ∣ wheel840)).symm
  have h3 : Nat.Coprime 3 n := (h.coprime_dvd_right (by native_decide : 3 ∣ wheel840)).symm
  have h5 : Nat.Coprime 5 n := (h.coprime_dvd_right (by native_decide : 5 ∣ wheel840)).symm
  have h7 : Nat.Coprime 7 n := (h.coprime_dvd_right (by native_decide : 7 ∣ wheel840)).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Nat.Prime.coprime_iff_not_dvd prime_two).1 h2
  · exact (Nat.Prime.coprime_iff_not_dvd prime_three).1 h3
  · exact (Nat.Prime.coprime_iff_not_dvd prime_five).1 h5
  · exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 7)).1 h7

/-! ### Complement: rejection when not coprime -/

/-- Any prime divisor of `wheel840` is one of `2,3,5,7`. -/
theorem prime_dvd_wheel840 {p : ℕ} (hp : Prime p) (h : p ∣ wheel840) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hp' : Nat.Prime p := (prime_iff p).1 hp
  have h840 : p ∣ (840 : ℕ) := by
    simpa [wheel840] using h
  have hprod : p ∣ 2^3 * 3 * 5 * 7 := by
    simpa [wheel840_factorization] using h840
  have h1 : p ∣ (2^3 * 3 * 5) ∨ p ∣ 7 := (hp'.dvd_mul).1 hprod
  rcases h1 with h235 | h7
  · have h2 : p ∣ (2^3 * 3) ∨ p ∣ 5 := (hp'.dvd_mul).1 h235
    rcases h2 with h23 | h5
    · have h3 : p ∣ 2^3 ∨ p ∣ 3 := (hp'.dvd_mul).1 h23
      rcases h3 with h2pow | h3
      · have h2 : p ∣ 2 := hp'.dvd_of_dvd_pow (m := 2) (n := 3) h2pow
        exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp' prime_two).1 h2)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp' prime_three).1 h3))
    ·
      have h5prime : Nat.Prime 5 := (prime_iff 5).1 prime_five
      exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp' h5prime).1 h5)))
  ·
    have h7prime : Nat.Prime 7 := by decide
    exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp' h7prime).1 h7)))

/-- If `n` is **not** coprime to `840`, then at least one of `2,3,5,7` divides `n`. -/
theorem wheel840_rejects (n : ℕ) (h : ¬ Nat.Coprime n wheel840) :
    2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n ∨ 7 ∣ n := by
  have hg_ne_one : Nat.gcd n wheel840 ≠ 1 := by
    intro hg
    apply h
    exact (Nat.coprime_iff_gcd_eq_one).2 hg
  obtain ⟨p, hpprime, hpdvg⟩ :=
    (Nat.ne_one_iff_exists_prime_dvd (n := Nat.gcd n wheel840)).1 hg_ne_one
  have hpdvn : p ∣ n := hpdvg.trans (Nat.gcd_dvd_left n wheel840)
  have hpdv840 : p ∣ wheel840 := hpdvg.trans (Nat.gcd_dvd_right n wheel840)
  have hp : Prime p := by
    simpa [Prime] using hpprime
  have hp_cases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 :=
    prime_dvd_wheel840 (p := p) hp hpdv840
  rcases hp_cases with hp2 | hp_rest
  · left
    simpa [hp2] using hpdvn
  · rcases hp_rest with hp3 | hp_rest2
    · exact Or.inr (Or.inl (by simpa [hp3] using hpdvn))
    · rcases hp_rest2 with hp5 | hp7
      · exact Or.inr (Or.inr (Or.inl (by simpa [hp5] using hpdvn)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [hp7] using hpdvn)))

/-- A gcd-form of `wheel840_rejects` (sometimes more convenient in proofs). -/
theorem wheel840_rejects_of_gcd_ne_one (n : ℕ) (h : Nat.gcd n wheel840 ≠ 1) :
    2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n ∨ 7 ∣ n := by
  apply wheel840_rejects (n := n)
  intro hc
  apply h
  exact (Nat.coprime_iff_gcd_eq_one).1 hc

end Primes
end NumberTheory
end IndisputableMonolith

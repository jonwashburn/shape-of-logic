import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic
import IndisputableMonolith.NumberTheory.Primes.Factorization

/-!
# RS constants (prime facts and factorizations)

This file collects small, **decidable** arithmetic facts about integers that appear repeatedly in
the `reality` repo (e.g. `8`, `45`, `360`, `840`, and prime markers like `11`, `17`, `37`, `103`,
`137`).

These are intentionally “boring but stable” anchors: they keep later bridge lemmas readable and
avoid re-proving the same arithmetic in many places.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

/-! ### Prime facts (small constants) -/

theorem prime_five : Prime 5 := by
  decide

theorem prime_eleven : Prime 11 := by
  decide

theorem prime_seventeen : Prime 17 := by
  decide

theorem prime_thirtyseven : Prime 37 := by
  decide

theorem prime_onehundredthree : Prime 103 := by
  decide

theorem prime_onehundredthirtyseven : Prime 137 := by
  decide

/-! ### GCD/LCM and factorizations (RS cycle integers) -/

theorem eight_eq_two_pow_three : (8 : ℕ) = 2^3 := by
  native_decide

theorem fortyfive_eq_three_sq_mul_five : (45 : ℕ) = 3^2 * 5 := by
  native_decide

theorem gcd_eight_fortyfive_eq_one : Nat.gcd 8 45 = 1 := by
  native_decide

theorem lcm_eight_fortyfive_eq_360 : Nat.lcm 8 45 = 360 := by
  native_decide

theorem threehundredsixty_factorization : (360 : ℕ) = 2^3 * 3^2 * 5 := by
  native_decide

theorem wheel840_factorization : (840 : ℕ) = 2^3 * 3 * 5 * 7 := by
  native_decide

/-! ### Rational identities (beat-frequency arithmetic) -/

theorem one_div_eight_sub_one_div_fortyfive :
    (1 : ℚ) / 8 - (1 : ℚ) / 45 = (37 : ℚ) / 360 := by
  norm_num

theorem aliasing_ratio : (37 : ℚ) / 45 < 1 := by
  norm_num

/-! ### Integer identities (beat numerator as a difference) -/

/-- The RS beat numerator arises as a simple difference: \(45 - 8 = 37\). -/
theorem fortyfive_sub_eight_eq_thirtyseven : (45 : ℕ) - 8 = 37 := by
  native_decide

/-- Convenience wrapper: 8 and 45 are coprime. -/
theorem coprime_eight_fortyfive : Nat.Coprime 8 45 := by
  native_decide

/-! ### vp-based characterizations of RS constants -/

/-- The prime spectrum of 8: only has 2-content, with exponent 3. -/
theorem vp_eight_two : vp 2 8 = 3 := by native_decide
theorem vp_eight_three : vp 3 8 = 0 := by native_decide
theorem vp_eight_five : vp 5 8 = 0 := by native_decide

/-- The prime spectrum of 45: has 3-content (exponent 2) and 5-content (exponent 1). -/
theorem vp_fortyfive_two : vp 2 45 = 0 := by native_decide
theorem vp_fortyfive_three : vp 3 45 = 2 := by native_decide
theorem vp_fortyfive_five : vp 5 45 = 1 := by native_decide

/-- The prime spectrum of 360: the full LCM uses all three primes {2, 3, 5}. -/
theorem vp_360_two : vp 2 360 = 3 := by native_decide
theorem vp_360_three : vp 3 360 = 2 := by native_decide
theorem vp_360_five : vp 5 360 = 1 := by native_decide
theorem vp_360_seven : vp 7 360 = 0 := by native_decide

/-- The prime spectrum of 840 (wheel modulus): uses {2, 3, 5, 7}. -/
theorem vp_840_two : vp 2 840 = 3 := by native_decide
theorem vp_840_three : vp 3 840 = 1 := by native_decide
theorem vp_840_five : vp 5 840 = 1 := by native_decide
theorem vp_840_seven : vp 7 840 = 1 := by native_decide

/-- 360 = lcm(8, 45) via the vp characterization: max at each prime. -/
theorem lcm_eight_fortyfive_vp_characterization (p : ℕ) :
    vp p 360 = max (vp p 8) (vp p 45) := by
  have h360 : (360 : ℕ) ≠ 0 := by decide
  have h8 : (8 : ℕ) ≠ 0 := by decide
  have h45 : (45 : ℕ) ≠ 0 := by decide
  rw [← lcm_eight_fortyfive_eq_360]
  exact vp_lcm h8 h45 p

/-- 8 and 45 are coprime: their gcd has vp = 0 everywhere. -/
theorem coprime_eight_fortyfive_vp (p : ℕ) : vp p (Nat.gcd 8 45) = 0 := by
  rw [gcd_eight_fortyfive_eq_one]
  simp

/-- The beat frequency numerator 37 is prime. -/
theorem prime_beat_numerator : Prime 37 := prime_thirtyseven

/-- 37 does not divide 360 (since gcd(37, 360) = 1). -/
theorem coprime_thirtyseven_360 : Nat.Coprime 37 360 := by native_decide

/-! ### Additional RS primes and constants -/

/-- The number 13 is prime (cicada cycle). -/
theorem prime_thirteen : Prime 13 := by decide

/-- The number 7 is prime (wheel factor). -/
theorem prime_seven : Prime 7 := by decide

/-- The cycle-45 gap is squarefree: 45 = 3² · 5, but wait—45 is NOT squarefree because 3² divides it.
We record the correct statement: 45 is not squarefree. -/
theorem not_squarefree_fortyfive : ¬Squarefree 45 := by
  intro hsq
  have h := hsq 3 ⟨5, by norm_num⟩
  simp at h

/-- 360 is not squarefree (since 4 = 2² divides it). -/
theorem not_squarefree_360 : ¬Squarefree 360 := by
  intro hsq
  have h := hsq 2 ⟨90, by norm_num⟩
  simp at h

/-- 8 is not squarefree (since 4 = 2² divides it). -/
theorem not_squarefree_eight : ¬Squarefree 8 := by
  intro hsq
  have h := hsq 2 ⟨2, by norm_num⟩
  simp at h

/-- 840 is not squarefree (since 4 = 2² divides it). -/
theorem not_squarefree_840 : ¬Squarefree 840 := by
  intro hsq
  have h := hsq 2 ⟨210, by norm_num⟩
  simp at h

/-- The radical of 360 (product of distinct prime factors) is 30 = 2·3·5. -/
theorem radical_360 : (360 : ℕ).primeFactors.prod id = 30 := by native_decide

/-- The radical of 8 is 2. -/
theorem radical_eight : (8 : ℕ).primeFactors.prod id = 2 := by native_decide

/-- The radical of 45 is 15 = 3·5. -/
theorem radical_fortyfive : (45 : ℕ).primeFactors.prod id = 15 := by native_decide

/-! ### Divisibility facts for RS constants -/

/-- 8 divides 360. -/
theorem eight_dvd_360 : 8 ∣ 360 := by decide

/-- 45 divides 360. -/
theorem fortyfive_dvd_360 : 45 ∣ 360 := by decide

/-- 360 / 8 = 45. -/
theorem threehundredsixty_div_eight : 360 / 8 = 45 := by native_decide

/-- 360 / 45 = 8. -/
theorem threehundredsixty_div_fortyfive : 360 / 45 = 8 := by native_decide

end Primes
end NumberTheory
end IndisputableMonolith

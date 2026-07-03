import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic

/-!
# Resonance and Cycle Dynamics

This module formalizes the "Cicada Principle" and other resonance phenomena
where primes play a structural role in minimizing or maximizing alignment.

## The Cicada Principle

Periodical cicadas (Magicicada) appear in 13- and 17-year cycles. These are prime numbers.
This strategy minimizes the frequency of intersection with predator lifecycles.

If a predator has a cycle `k`, it meets the cicada every `lcm(p, k)` years.
If `p` is prime and `¬ p ∣ k`, then `lcm(p, k) = p * k`.
This maximizes the "safety window" compared to composite cycles.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

open Nat

/-- **The Cicada Lemma**:
    If `p` is prime and does not divide `k`, then their first synchronization
    (LCM) occurs at exactly `p * k`.

    This maximizes the time between encounters. -/
theorem cicada_safety_interval (p k : ℕ) (hp : Prime p) (h_ndvd : ¬ p ∣ k) :
    Nat.lcm p k = p * k := by
  -- Since p is prime and does not divide k, gcd(p, k) must be 1.
  have h_coprime : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).mpr h_ndvd
  have h_gcd : Nat.gcd p k = 1 := h_coprime
  -- Use gcd * lcm = a * b
  have h_mul := Nat.gcd_mul_lcm p k
  rw [h_gcd, one_mul] at h_mul
  exact h_mul

/-- The "safety ratio" is maximized when cycles are coprime.
    Safety ratio = LCM(p, k) / k = p (the max possible value). -/
def safety_ratio (p k : ℕ) : ℚ := (Nat.lcm p k : ℚ) / (k : ℚ)

theorem max_safety_ratio (p k : ℕ) (hp : Prime p) (hk : k > 0) (h_ndvd : ¬ p ∣ k) :
    safety_ratio p k = p := by
  rw [safety_ratio, cicada_safety_interval p k hp h_ndvd]
  have hk_q_pos : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  rw [mul_comm p k]
  simp only [Nat.cast_mul]
  field_simp [hk_q_pos]

end Primes
end NumberTheory
end IndisputableMonolith

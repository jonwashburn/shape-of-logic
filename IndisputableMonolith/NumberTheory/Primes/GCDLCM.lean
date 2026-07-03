import Mathlib
import IndisputableMonolith.NumberTheory.Primes.Basic

/-!
# GCD/LCM utilities (prime-friendly)

This file centralizes small gcd/lcm algebra lemmas we’ll reuse across the primes framework.
Most statements are already in Mathlib, but we expose stable wrappers in our namespace.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace Primes

open Nat

/-- If `a` and `b` are coprime, then `lcm a b = a * b`. -/
theorem coprime_lcm_eq_mul (a b : ℕ) (h : Nat.Coprime a b) : Nat.lcm a b = a * b := by
  have hgcd : Nat.gcd a b = 1 := h
  simpa [hgcd] using (Nat.gcd_mul_lcm a b)

/-- `gcd a b * lcm a b = a * b` (a standard arithmetic identity). -/
theorem gcd_mul_lcm (a b : ℕ) : Nat.gcd a b * Nat.lcm a b = a * b := by
  exact Nat.gcd_mul_lcm a b

/-! ### Casted lcm formulas (for analytic work) -/

/-- A casted form of `gcd_mul_lcm`:
\[
(\gcd(a,b) : \mathbb{Q}) \cdot (\operatorname{lcm}(a,b) : \mathbb{Q}) = (a b : \mathbb{Q}).
\]
-/
theorem gcd_mul_lcm_cast (a b : ℕ) :
    (Nat.gcd a b : ℚ) * (Nat.lcm a b : ℚ) = (a * b : ℚ) := by
  norm_cast
  exact gcd_mul_lcm a b

/-- For `gcd(a,b) ≠ 0`, we can solve for `lcm` in `ℚ`:
\[
(\operatorname{lcm}(a,b) : \mathbb{Q}) = \frac{ab}{\gcd(a,b)}.
\]
-/
theorem lcm_cast_eq_mul_div_gcd (a b : ℕ) (h : Nat.gcd a b ≠ 0) :
    (Nat.lcm a b : ℚ) = (a * b : ℚ) / (Nat.gcd a b : ℚ) := by
  have hgcd_q : (Nat.gcd a b : ℚ) ≠ 0 := by
    exact_mod_cast h
  -- Multiply both sides by `gcd` and use `gcd_mul_lcm_cast`.
  apply (mul_left_cancel₀ hgcd_q)
  -- LHS: gcd * lcm ; RHS: gcd * (ab/gcd) = ab
  -- Use `gcd_mul_lcm_cast` and `mul_div_cancel₀`.
  calc
    (Nat.gcd a b : ℚ) * (Nat.lcm a b : ℚ)
        = (a * b : ℚ) := gcd_mul_lcm_cast a b
    _ = (Nat.gcd a b : ℚ) * ((a * b : ℚ) / (Nat.gcd a b : ℚ)) := by
        -- `gcd * (ab / gcd) = ab`
        symm
        simpa [div_eq_mul_inv, mul_assoc] using (mul_div_cancel₀ (a := (a * b : ℚ)) hgcd_q)

end Primes
end NumberTheory
end IndisputableMonolith

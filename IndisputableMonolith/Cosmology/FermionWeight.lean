import Mathlib
import IndisputableMonolith.Cosmology.EntropyPerPhoton

/-!
# The 7/8 Fermion Entropy Weight from the Eta/Zeta Series Identity

**Status: THEOREM (series layer).**

This module upgrades the `fermionWeight = 7/8` MODEL input of
`Cosmology.EntropyPerPhoton` to a derived identity at the series level:

  `η(4) = (7/8) · ζ(4)`,

where `ζ(4) = ∑ 1/n⁴ = π⁴/90` (Mathlib's `hasSum_zeta_four`) and
`η(4) = ∑ (−1)^(n+1)/n⁴` is the Dirichlet eta value that controls the
Fermi–Dirac thermodynamic integral `∫ x³/(eˣ+1) dx = Γ(4)·η(4)` (the
Bose–Einstein integral being `∫ x³/(eˣ−1) dx = Γ(4)·ζ(4)`; the integral
layer lives in `Cosmology.FermionWeightIntegral`).

## Derivation

Split `ζ(4)` into even- and odd-index parts:

  even: `∑ 1/(2k)⁴ = (1/16)·ζ(4)`   (n = 2k re-indexing, k = 0 term vanishes)
  odd:  `∑ 1/(2k+1)⁴ = (15/16)·ζ(4)` (by subtraction and uniqueness of sums)

Then the alternating series is odd-part minus even-part:

  `η(4) = (15/16)·ζ(4) − (1/16)·ζ(4) = (14/16)·ζ(4) = (7/8)·ζ(4)`.

All sums are unconditional (`HasSum` over ℕ); the even/odd recombination is
Mathlib's `HasSum.even_add_odd`; no axioms beyond Lean's base three.

The final theorem `fermionWeight_eq_eta_zeta_ratio` states that the rational
`7/8` used in `EntropyPerPhoton.fermionWeight` is exactly `η(4)/ζ(4)`, which
removes "the eta/zeta series identity is classical" from the MODEL-input list
(the remaining MODEL content of the weight is only the *statistical mechanics*
statement that a fermion species contributes the Fermi–Dirac integral, i.e.
the physics input, not the mathematics).
-/

namespace IndisputableMonolith
namespace Cosmology
namespace FermionWeight

open Real

/-! ## §1. Even part: `∑ 1/(2k)⁴ = ζ(4)/16` -/

/-- Pointwise identity `1/(2k)⁴ = (1/k⁴)/16`, including `k = 0` where both
sides are `0` (division by zero). -/
lemma even_term_eq :
    (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 4)
      = fun k : ℕ => ((1 : ℝ) / (k : ℝ) ^ 4) / 16 := by
  funext k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    push_cast
    field_simp
    ring

/-- The even-index part of `ζ(4)`: `∑_k 1/(2k)⁴ = (π⁴/90)/16`. -/
lemma hasSum_even :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 4) (π ^ 4 / 90 / 16) := by
  rw [even_term_eq]
  exact hasSum_zeta_four.div_const 16

/-! ## §2. Odd part: `∑ 1/(2k+1)⁴ = (15/16)·ζ(4)` -/

lemma summable_odd :
    Summable (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 4) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) := hasSum_zeta_four.summable
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab
    simp only at hab
    omega
  have h2 := h.comp_injective hinj
  exact h2.congr fun k => by simp only [Function.comp_apply]

/-- The odd-index part of `ζ(4)`: `∑_k 1/(2k+1)⁴ = (π⁴/90)·(15/16)`.
Derived by subtraction: full sum minus even part, using uniqueness of
unconditional sums in ℝ. -/
lemma hasSum_odd :
    HasSum (fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
      (π ^ 4 / 90 * (15 / 16)) := by
  obtain ⟨B, hB⟩ := summable_odd
  have hfull : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) (π ^ 4 / 90 / 16 + B) :=
    HasSum.even_add_odd hasSum_even hB
  have hval : π ^ 4 / 90 / 16 + B = π ^ 4 / 90 := hfull.unique hasSum_zeta_four
  have hBval : B = π ^ 4 / 90 * (15 / 16) := by linarith
  exact hBval ▸ hB

/-! ## §3. The alternating (eta) series -/

/-- Even-index terms of the alternating series are negatives of the
even-`ζ` terms: `(−1)^(2k+1)/(2k)⁴ = −1/(2k)⁴`. -/
lemma eta_term_even (k : ℕ) :
    ((-1 : ℝ)) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 4
      = -((1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 4) := by
  rw [(odd_two_mul_add_one k).neg_one_pow]
  push_cast
  ring

/-- Odd-index terms of the alternating series are the odd-`ζ` terms:
`(−1)^(2k+2)/(2k+1)⁴ = 1/(2k+1)⁴`. -/
lemma eta_term_odd (k : ℕ) :
    ((-1 : ℝ)) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 4
      = (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 4 := by
  have heven : Even (2 * k + 1 + 1) := ⟨k + 1, by ring⟩
  rw [heven.neg_one_pow]

/-- **THEOREM (η(4) as a `HasSum`).** The alternating series
`∑ (−1)^(n+1)/n⁴` converges unconditionally to `(7/8)·(π⁴/90)`,
i.e. `η(4) = (7/8)·ζ(4)`. -/
theorem hasSum_eta_four :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4)
      (7 / 8 * (π ^ 4 / 90)) := by
  have he : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 4)
      (-(π ^ 4 / 90 / 16)) := by
    have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ 4)
        = fun k : ℕ => -((1 : ℝ) / ((2 * k : ℕ) : ℝ) ^ 4) := by
      funext k; exact eta_term_even k
    rw [hfun]
    exact hasSum_even.neg
  have ho : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
      (π ^ 4 / 90 * (15 / 16)) := by
    have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 4)
        = fun k : ℕ => (1 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 4 := by
      funext k; exact eta_term_odd k
    rw [hfun]
    exact hasSum_odd
  have h := HasSum.even_add_odd
    (f := fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4) he ho
  convert h using 1
  ring

/-- **THEOREM (the eta/zeta ratio).** `η(4) / ζ(4) = 7/8` as real numbers. -/
theorem eta4_div_zeta4 :
    (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4)
      / (∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4) = 7 / 8 := by
  rw [hasSum_eta_four.tsum_eq, hasSum_zeta_four.tsum_eq]
  have hz : (π : ℝ) ^ 4 / 90 ≠ 0 := by positivity
  rw [mul_div_assoc, div_self hz, mul_one]

/-- **THEOREM (fermion weight provenance).** The `7/8` MODEL constant in
`EntropyPerPhoton.fermionWeight` is exactly the eta/zeta ratio:
`fermionWeight · ζ(4) = η(4)`. The series identity is now derived, not
imported; the remaining MODEL content of the weight is only the
statistical-mechanics identification of the fermionic entropy integral. -/
theorem fermionWeight_eq_eta_zeta_ratio :
    ((EntropyPerPhoton.fermionWeight : ℚ) : ℝ)
        * ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 4
      = ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 := by
  rw [hasSum_eta_four.tsum_eq, hasSum_zeta_four.tsum_eq]
  unfold EntropyPerPhoton.fermionWeight
  push_cast
  ring

end FermionWeight
end Cosmology
end IndisputableMonolith

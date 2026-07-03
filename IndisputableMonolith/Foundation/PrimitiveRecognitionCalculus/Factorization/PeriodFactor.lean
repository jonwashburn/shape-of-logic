/-
  PrimitiveRecognitionCalculus/Factorization/PeriodFactor.lean

  The gcd-extraction step of period-based factoring, proved (not stored). Given
  a half-period element `b = a^(r/2)` with `b^2 ≡ 1 (mod N)` but `b ≢ ±1`, the
  gcd `gcd(b - 1, N)` is a proper nontrivial divisor of `N`. This is the content
  Shor's algorithm reads after period finding; here it is a δ theorem, not a
  device hypothesis.

  This closes the A3 exit claim. It says nothing about the cost of producing the
  period `r`; that remains the open performance lane.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PeriodSpectrum

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-! ## Nat-level gcd extraction -/

/-- The square-difference factorization holds in `ℕ` truncated subtraction for
`b ≥ 1`. -/
theorem sub_mul_add_eq_sq_sub_one {b : ℕ} (hb : 1 ≤ b) :
    (b - 1) * (b + 1) = b ^ 2 - 1 := by
  have key : (b - 1) * (b + 1) + 1 = b * b := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb
    rw [Nat.add_sub_cancel_left]
    ring
  have hfac : (b - 1) * (b + 1) = b * b - 1 := Nat.eq_sub_of_add_eq key
  rw [hfac, pow_two]

/-- Even-period factor extraction. If `b^2 ≡ 1 (mod n)` while `b ≢ 1` and
`b ≢ -1 (mod n)`, then `gcd(b - 1, n)` is strictly between `1` and `n`, hence a
proper nontrivial divisor of `n`. -/
theorem even_period_yields_factor
    {n b : ℕ} (hn : 2 ≤ n) (hb : 1 ≤ b)
    (hsq : n ∣ b ^ 2 - 1)
    (hm1 : ¬ n ∣ (b - 1))
    (hp1 : ¬ n ∣ (b + 1)) :
    1 < Nat.gcd (b - 1) n ∧ Nat.gcd (b - 1) n < n := by
  have hfac : (b - 1) * (b + 1) = b ^ 2 - 1 := sub_mul_add_eq_sq_sub_one hb
  have hdvd_prod : n ∣ (b - 1) * (b + 1) := by
    rw [hfac]; exact hsq
  have hgdvdN : Nat.gcd (b - 1) n ∣ n := Nat.gcd_dvd_right (b - 1) n
  have hgne_n : Nat.gcd (b - 1) n ≠ n := by
    intro h
    apply hm1
    have hgL : Nat.gcd (b - 1) n ∣ (b - 1) := Nat.gcd_dvd_left (b - 1) n
    rw [h] at hgL
    exact hgL
  have hg_lt : Nat.gcd (b - 1) n < n :=
    lt_of_le_of_ne (Nat.le_of_dvd (by omega) hgdvdN) hgne_n
  have hg_ne1 : Nat.gcd (b - 1) n ≠ 1 := by
    intro h
    have hcop : Nat.Coprime (b - 1) n := h
    have hn_dvd : n ∣ (b + 1) := hcop.symm.dvd_of_dvd_mul_left hdvd_prod
    exact hp1 hn_dvd
  have hg_pos : 0 < Nat.gcd (b - 1) n :=
    Nat.gcd_pos_iff.mpr (Or.inr (by omega))
  exact ⟨by omega, hg_lt⟩

/-! ## δ-level corollary -/

/-- δ form: an even-period gap on `N` produces a native nontrivial factorization
of `N`, with the extracted divisor `ofNat (gcd(b - 1, N))`. The hypotheses are
exactly what a certified period witness supplies through the residue display. -/
theorem nontrivialFactorization_of_even_period_gap
    {N b : DistinctionNat} (hN : N ≠ zero) (hN2 : 2 ≤ N.toNat)
    (hb1 : 1 ≤ b.toNat)
    (hsq : N.toNat ∣ b.toNat ^ 2 - 1)
    (hm1 : ¬ N.toNat ∣ (b.toNat - 1))
    (hp1 : ¬ N.toNat ∣ (b.toNat + 1)) :
    nontrivialFactorization N := by
  obtain ⟨hg1, hglt⟩ := even_period_yields_factor hN2 hb1 hsq hm1 hp1
  have hgdvdN : Nat.gcd (b.toNat - 1) N.toNat ∣ N.toNat :=
    Nat.gcd_dvd_right _ _
  refine nontrivialFactorization_of_proper_divisor
    (d := ofNat (Nat.gcd (b.toNat - 1) N.toNat)) hN ?_ ?_ ?_ ?_
  · intro h
    have hh := congrArg DistinctionNat.toNat h
    rw [toNat_ofNat, toNat_zero] at hh
    omega
  · rw [unit_iff_toNat_eq_one, toNat_ofNat]
    omega
  · intro h
    have hh := congrArg DistinctionNat.toNat h
    rw [toNat_ofNat] at hh
    omega
  · rw [divides_iff_toNat_dvd, toNat_ofNat]
    exact hgdvdN

/-- Certificate for the period-factor extraction surface. -/
structure PeriodFactorCertificate : Prop where
  nat_even_period_extracts :
    ∀ {n b : ℕ}, 2 ≤ n → 1 ≤ b → n ∣ b ^ 2 - 1 →
      ¬ n ∣ (b - 1) → ¬ n ∣ (b + 1) →
        1 < Nat.gcd (b - 1) n ∧ Nat.gcd (b - 1) n < n
  delta_even_period_factorizes :
    ∀ {N b : DistinctionNat}, N ≠ zero → 2 ≤ N.toNat → 1 ≤ b.toNat →
      N.toNat ∣ b.toNat ^ 2 - 1 →
      ¬ N.toNat ∣ (b.toNat - 1) → ¬ N.toNat ∣ (b.toNat + 1) →
        nontrivialFactorization N

theorem period_factor_certificate : PeriodFactorCertificate where
  nat_even_period_extracts := by
    intro n b hn hb hsq hm1 hp1
    exact even_period_yields_factor hn hb hsq hm1 hp1
  delta_even_period_factorizes := by
    intro N b hN hN2 hb1 hsq hm1 hp1
    exact nontrivialFactorization_of_even_period_gap hN hN2 hb1 hsq hm1 hp1

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

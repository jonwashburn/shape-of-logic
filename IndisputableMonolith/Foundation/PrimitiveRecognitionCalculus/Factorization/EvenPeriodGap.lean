/-
  PrimitiveRecognitionCalculus/Factorization/EvenPeriodGap.lean

  Capstone of the period-to-factor chain. With period existence (Euler, in
  `PeriodExistence`) and gcd extraction (in `PeriodFactor`) both proved, the only
  remaining link is the existence of a unit residue whose period is even and
  whose half-power avoids ±1. This file proves the conditional closure: such a
  witness yields a nontrivial factorization. It names the existence as the single
  open lane (the δ form of Shor's success condition), and does not assert it.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PeriodFactor

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- A unit residue with an even-period gap: `base` has a full period `half + half`
returning to the identity, while the half-power avoids both `1` and `-1` modulo
`N`. This is exactly the configuration Shor's algorithm needs after period
finding. -/
structure EvenPeriodGapWitness (N : DistinctionNat) (hN : N ≠ zero) : Type where
  base : DistinctionNat
  half : DistinctionNat
  base_unit : unitResidue N base
  full_period : sameResidue N hN (orbitPow base (half + half)) one
  half_not_one : ¬ N.toNat ∣ ((orbitPow base half).toNat - 1)
  half_not_neg_one : ¬ N.toNat ∣ ((orbitPow base half).toNat + 1)

/-- The conditional closure: an even-period-gap witness produces a native
nontrivial factorization of `N`. This reduces period-based factoring to a single
existence statement. -/
theorem nontrivialFactorization_of_evenPeriodGapWitness {N : DistinctionNat}
    {hN : N ≠ zero} (hN2 : 2 ≤ N.toNat) (w : EvenPeriodGapWitness N hN) :
    nontrivialFactorization N := by
  have hbase_pos : 1 ≤ w.base.toNat := by
    have hcop := (unitResidue_iff_nat_coprime N w.base).mp w.base_unit
    rcases Nat.eq_zero_or_pos w.base.toNat with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop
      omega
    · omega
  have hb1 : 1 ≤ (orbitPow w.base w.half).toNat := by
    rw [orbitPow_toNat]
    exact Nat.one_le_pow _ _ hbase_pos
  have hsqeq : (orbitPow w.base (w.half + w.half)).toNat
      = (orbitPow w.base w.half).toNat ^ 2 := by
    rw [orbitPow_toNat, orbitPow_toNat, toNat_add, pow_two, ← pow_add]
  have hmod : (orbitPow w.base (w.half + w.half)).toNat % N.toNat = 1 % N.toNat := by
    have hp := (sameResidue_iff_mod_eq N hN _ _).mp w.full_period
    rwa [one_toNat] at hp
  have hsq : N.toNat ∣ (orbitPow w.base w.half).toNat ^ 2 - 1 := by
    rw [← hsqeq]
    have hge : 1 ≤ (orbitPow w.base (w.half + w.half)).toNat := by
      rw [hsqeq]
      exact Nat.one_le_pow _ _ hb1
    rw [← Nat.modEq_iff_dvd' hge]
    exact hmod.symm
  exact nontrivialFactorization_of_even_period_gap hN hN2 hb1 hsq
    w.half_not_one w.half_not_neg_one

/-- The single open lane, stated precisely: for the modulus `N`, does a unit
residue with an even-period gap exist? This is the δ form of Shor's success
condition. It is OPEN here. Proving it (the ≥ 1/2 counting bound over the unit
group of a composite with at least two distinct odd prime factors) would close
period-based factoring end to end. This definition asserts nothing; it only
names the residual. -/
def EvenPeriodGapExists (N : DistinctionNat) (hN : N ≠ zero) : Prop :=
  Nonempty (EvenPeriodGapWitness N hN)

/-- If the open existence holds for `N`, then `N` has a nontrivial factorization.
The reduction is unconditional; only the existence input is open. -/
theorem nontrivialFactorization_of_evenPeriodGapExists {N : DistinctionNat}
    {hN : N ≠ zero} (hN2 : 2 ≤ N.toNat) (h : EvenPeriodGapExists N hN) :
    nontrivialFactorization N := by
  obtain ⟨w⟩ := h
  exact nontrivialFactorization_of_evenPeriodGapWitness hN2 w

/-- Certificate for the even-period-gap reduction. It records the proved
conditional and is explicit that the existence input is not supplied here. -/
structure EvenPeriodGapCertificate : Prop where
  witness_factorizes :
    ∀ {N : DistinctionNat} {hN : N ≠ zero}, 2 ≤ N.toNat →
      EvenPeriodGapWitness N hN → nontrivialFactorization N
  existence_reduces_to_factorization :
    ∀ {N : DistinctionNat} {hN : N ≠ zero}, 2 ≤ N.toNat →
      EvenPeriodGapExists N hN → nontrivialFactorization N

theorem even_period_gap_certificate : EvenPeriodGapCertificate where
  witness_factorizes := by
    intro N hN hN2 w
    exact nontrivialFactorization_of_evenPeriodGapWitness hN2 w
  existence_reduces_to_factorization := by
    intro N hN hN2 h
    exact nontrivialFactorization_of_evenPeriodGapExists hN2 h

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

/-
  PrimitiveRecognitionCalculus/Factorization/PeriodSpectrum.lean

  Multiplicative powers and certified period witnesses for unit residues.
  This file does not assert a fast period-finder. It only defines the witness
  object that any classical, quantum, or physical readout must return.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.UnitGroup

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- δ-native exponentiation by an orbit exponent. -/
def orbitPow (a : DistinctionNat) : DistinctionNat → DistinctionNat
  | zero => one
  | succ k => orbitPow a k * a

theorem orbitPow_zero (a : DistinctionNat) :
    orbitPow a zero = one := rfl

theorem orbitPow_succ (a k : DistinctionNat) :
    orbitPow a (succ k) = orbitPow a k * a := rfl

theorem orbitPow_toNat (a k : DistinctionNat) :
    (orbitPow a k).toNat = a.toNat ^ k.toNat := by
  induction k with
  | zero =>
      simp [orbitPow, one_toNat]
  | succ k ih =>
      rw [orbitPow_succ, toNat_mul, ih, toNat_succ]
      exact Nat.pow_succ a.toNat k.toNat

theorem orbitPow_unitResidue {N a : DistinctionNat}
    (ha : unitResidue N a) (k : DistinctionNat) :
    unitResidue N (orbitPow a k) := by
  rw [unitResidue_iff_nat_coprime]
  rw [orbitPow_toNat]
  exact unitResidue_pow_closed ha k.toNat

/-- A certified period witness. Minimality is optional at the interface; the
essential output is a nonzero exponent that returns the unit residue to `1`. -/
structure PeriodWitness (N : DistinctionNat) (hN : N ≠ zero)
    (a r : DistinctionNat) : Prop where
  exponent_nonzero : r ≠ zero
  base_unit : unitResidue N a
  returns_one : sameResidue N hN (orbitPow a r) one

/-- A period witness plus a proper divisor it exposes. The divisor may come
from the usual `gcd(a^(r/2)-1,N)` route, but this structure deliberately stores
the certificate rather than pretending the readout itself is already derived. -/
structure ProperDivisorFromPeriod (N : DistinctionNat) (hN : N ≠ zero)
    (a r : DistinctionNat) : Type where
  period : PeriodWitness N hN a r
  divisor : DistinctionNat
  divisor_nonzero : divisor ≠ zero
  divisor_nonunit : ¬ unit divisor
  divisor_not_modulus : divisor ≠ N
  divisor_divides : divides divisor N

/-- Once a period readout has supplied a proper divisor certificate, the
δ-native divisibility layer gives a nontrivial factorization. -/
theorem period_divisor_to_nontrivialFactorization {N a r : DistinctionNat}
    {hN : N ≠ zero}
    (w : ProperDivisorFromPeriod N hN a r) :
    nontrivialFactorization N := by
  exact nontrivialFactorization_of_proper_divisor hN
    w.divisor_nonzero w.divisor_nonunit w.divisor_not_modulus
    w.divisor_divides

/-- Certificate for the period-spectrum interface. -/
structure PeriodSpectrumCertificate : Prop where
  pow_display :
    ∀ a k : DistinctionNat, (orbitPow a k).toNat = a.toNat ^ k.toNat
  pow_preserves_unit :
    ∀ {N a : DistinctionNat},
      unitResidue N a → ∀ k : DistinctionNat, unitResidue N (orbitPow a k)
  period_divisor_extracts_factorization :
    ∀ {N a r : DistinctionNat} {hN : N ≠ zero},
      ProperDivisorFromPeriod N hN a r → nontrivialFactorization N

theorem period_spectrum_certificate : PeriodSpectrumCertificate where
  pow_display := orbitPow_toNat
  pow_preserves_unit := by
    intro N a ha k
    exact orbitPow_unitResidue ha k
  period_divisor_extracts_factorization := by
    intro N a r hN w
    exact period_divisor_to_nontrivialFactorization w

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

/-
  PrimitiveRecognitionCalculus/Factorization/PeriodExistence.lean

  Every unit residue has a period. This is Euler/Fermat transported into the
  δ residue layer: for `a` coprime to `N`, `a^(totient N) ≡ 1 (mod N)`, so a
  certified `PeriodWitness` exists. It makes the period spectrum non-vacuous: the
  object a period-finder searches for always exists.

  This is existence, not cost. It says nothing about how cheaply the least period
  can be found; that is the open performance lane.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PeriodSpectrum

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- The Euler exponent of `N` as an orbit position: the totient of the display. -/
def periodExponent (N : DistinctionNat) : DistinctionNat :=
  ofNat (Nat.totient N.toNat)

theorem periodExponent_ne_zero {N : DistinctionNat} (hN2 : 2 ≤ N.toNat) :
    periodExponent N ≠ zero := by
  intro h
  have hh := congrArg DistinctionNat.toNat h
  rw [periodExponent, toNat_ofNat, toNat_zero] at hh
  have hpos : 0 < Nat.totient N.toNat := Nat.totient_pos.mpr (by omega)
  omega

/-- Euler's theorem in the δ residue layer: a unit residue raised to the Euler
exponent returns to the identity residue. -/
theorem eulerPeriod_returns_one {N a : DistinctionNat} (hN : N ≠ zero)
    (ha : unitResidue N a) :
    sameResidue N hN (orbitPow a (periodExponent N)) one := by
  rw [sameResidue_iff_mod_eq, orbitPow_toNat, periodExponent, toNat_ofNat,
    one_toNat]
  have hcop : Nat.Coprime a.toNat N.toNat :=
    (unitResidue_iff_nat_coprime N a).mp ha
  exact Nat.ModEq.pow_totient hcop

/-- Period existence: every unit residue modulo `N ≥ 2` has a certified period
witness, with period equal to the Euler exponent. -/
theorem period_exists_for_unitResidue {N a : DistinctionNat} (hN : N ≠ zero)
    (hN2 : 2 ≤ N.toNat) (ha : unitResidue N a) :
    PeriodWitness N hN a (periodExponent N) where
  exponent_nonzero := periodExponent_ne_zero hN2
  base_unit := ha
  returns_one := eulerPeriod_returns_one hN ha

theorem periodWitness_nonempty_of_unitResidue {N a : DistinctionNat}
    (hN : N ≠ zero) (hN2 : 2 ≤ N.toNat) (ha : unitResidue N a) :
    Nonempty (PeriodWitness N hN a (periodExponent N)) :=
  ⟨period_exists_for_unitResidue hN hN2 ha⟩

/-- Certificate for the period-existence surface. -/
structure PeriodExistenceCertificate : Prop where
  euler_period_returns_one :
    ∀ {N a : DistinctionNat} (hN : N ≠ zero),
      unitResidue N a →
        sameResidue N hN (orbitPow a (periodExponent N)) one
  period_exists :
    ∀ {N a : DistinctionNat} (hN : N ≠ zero), 2 ≤ N.toNat →
      unitResidue N a →
        Nonempty (PeriodWitness N hN a (periodExponent N))

theorem period_existence_certificate : PeriodExistenceCertificate where
  euler_period_returns_one := by
    intro N a hN ha
    exact eulerPeriod_returns_one hN ha
  period_exists := by
    intro N a hN hN2 ha
    exact periodWitness_nonempty_of_unitResidue hN hN2 ha

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

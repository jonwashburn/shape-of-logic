/-
  PrimitiveRecognitionCalculus/Factorization/UnitGroup.lean

  Unit residues modulo an orbit modulus. This is the first finite
  multiplicative surface needed for Dirichlet-style characters and period
  readout.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.ResidueOrbit

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- A residue representative is a unit modulo `N` when it is δ-coprime to `N`. -/
def unitResidue (N a : DistinctionNat) : Prop :=
  coprime a N

theorem unitResidue_iff_nat_coprime (N a : DistinctionNat) :
    unitResidue N a ↔ Nat.Coprime a.toNat N.toNat := by
  unfold unitResidue
  exact coprime_iff_nat_coprime a N

theorem unitResidue_one (N : DistinctionNat) :
    unitResidue N one := by
  rw [unitResidue_iff_nat_coprime, one_toNat]
  exact Nat.coprime_one_left N.toNat

theorem unitResidue_mul_closed {N a b : DistinctionNat}
    (ha : unitResidue N a) (hb : unitResidue N b) :
    unitResidue N (a * b) := by
  rw [unitResidue_iff_nat_coprime] at ha hb ⊢
  rw [toNat_mul]
  exact Nat.Coprime.mul_left ha hb

theorem unitResidue_pow_closed {N a : DistinctionNat}
    (ha : unitResidue N a) (k : Nat) :
    Nat.Coprime (a.toNat ^ k) N.toNat := by
  rw [unitResidue_iff_nat_coprime] at ha
  exact Nat.Coprime.pow_left k ha

/-- Unit residues form the carrier for finite multiplicative character theory. -/
structure UnitResidue (N : DistinctionNat) : Type where
  val : DistinctionNat
  isUnit : unitResidue N val

namespace UnitResidue

variable {N : DistinctionNat}

/-- The identity unit residue. -/
def one (N : DistinctionNat) : UnitResidue N where
  val := DistinctionNat.one
  isUnit := unitResidue_one N

/-- Multiplication of unit residues. -/
def mul (u v : UnitResidue N) : UnitResidue N where
  val := u.val * v.val
  isUnit := unitResidue_mul_closed u.isUnit v.isUnit

theorem mul_val (u v : UnitResidue N) :
    (mul u v).val = u.val * v.val := rfl

theorem one_val (N : DistinctionNat) :
    (one N).val = DistinctionNat.one := rfl

end UnitResidue

/-- Certificate for the unit-residue surface. -/
structure UnitGroupCertificate : Prop where
  unit_display :
    ∀ N a : DistinctionNat,
      unitResidue N a ↔ Nat.Coprime a.toNat N.toNat
  one_is_unit :
    ∀ N : DistinctionNat, unitResidue N one
  mul_closed :
    ∀ {N a b : DistinctionNat},
      unitResidue N a → unitResidue N b → unitResidue N (a * b)
  pow_closed_display :
    ∀ {N a : DistinctionNat},
      unitResidue N a → ∀ k : Nat, Nat.Coprime (a.toNat ^ k) N.toNat

theorem unit_group_certificate : UnitGroupCertificate where
  unit_display := unitResidue_iff_nat_coprime
  one_is_unit := unitResidue_one
  mul_closed := by
    intro N a b ha hb
    exact unitResidue_mul_closed ha hb
  pow_closed_display := by
    intro N a ha k
    exact unitResidue_pow_closed ha k

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Foundation.ArithmeticFromLogic
import IndisputableMonolith.NumberTheory.PrimeLedgerAtom

/-!
  LogicPrimeLedgerAtom.lean

  Logic-native prime ledger atoms.

  The first recovered-number adapter for the RH / prime-ledger stack:
  primality is stated on `LogicNat` and transported through the recovery
  equivalence `LogicNat.toNat`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace LogicPrimeLedgerAtom

open Foundation.ArithmeticFromLogic
open Foundation.ArithmeticFromLogic.LogicNat

/-- A prime ledger atom over recovered naturals. -/
def PrimeLedgerAtomLogic (p : LogicNat) : Prop :=
  PrimeLedgerAtom (toNat p)

/-- A recovered positive integer ledger state. -/
def IntegerLedgerStateLogic (n : LogicNat) : Prop :=
  0 < n

theorem primeLedgerAtomLogic_iff_prime (p : LogicNat) :
    PrimeLedgerAtomLogic p ↔ Nat.Prime (toNat p) :=
  primeLedgerAtom_iff_prime (toNat p)

theorem prime_is_ledger_atom_logic {p : LogicNat} (hp : Nat.Prime (toNat p)) :
    PrimeLedgerAtomLogic p :=
  (primeLedgerAtomLogic_iff_prime p).mpr hp

theorem ledger_atom_logic_is_prime {p : LogicNat} (h : PrimeLedgerAtomLogic p) :
    Nat.Prime (toNat p) :=
  (primeLedgerAtomLogic_iff_prime p).mp h

theorem one_not_primeLedgerAtomLogic :
    ¬ PrimeLedgerAtomLogic (fromNat 1) := by
  intro h
  have hp : Nat.Prime (toNat (fromNat 1)) := ledger_atom_logic_is_prime h
  rw [toNat_fromNat] at hp
  exact Nat.not_prime_one hp

theorem prime_logic_is_positive_ledger_state {p : LogicNat}
    (hp : Nat.Prime (toNat p)) : IntegerLedgerStateLogic p := by
  exact (toNat_lt LogicNat.zero p).mpr (by simpa [toNat_zero] using hp.pos)

/-- Certificate tying recovered-prime atoms to the classical prime ledger. -/
structure PrimeLedgerLogicCert where
  atom_iff_prime : ∀ p : LogicNat, PrimeLedgerAtomLogic p ↔ Nat.Prime (toNat p)
  one_not_atom : ¬ PrimeLedgerAtomLogic (fromNat 1)
  prime_positive : ∀ {p : LogicNat}, Nat.Prime (toNat p) → IntegerLedgerStateLogic p
  transports_classical : ∀ p : LogicNat, PrimeLedgerAtomLogic p ↔ PrimeLedgerAtom (toNat p)

def primeLedgerLogicCert : PrimeLedgerLogicCert where
  atom_iff_prime := primeLedgerAtomLogic_iff_prime
  one_not_atom := one_not_primeLedgerAtomLogic
  prime_positive := prime_logic_is_positive_ledger_state
  transports_classical := fun _ => Iff.rfl

end LogicPrimeLedgerAtom
end NumberTheory
end IndisputableMonolith

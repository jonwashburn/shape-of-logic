import Mathlib

/-!
# Prime Ledger Atoms

This module grounds the arithmetic ledger used by the RH bridge.

The content is deliberately classical and small: primes are exactly the
irreducible postings of the multiplicative positive-integer ledger.  The RS
work starts after this point, when the prime postings are weighted into the
Euler ledger.
-/

namespace IndisputableMonolith
namespace NumberTheory

/-- A prime ledger atom is a prime integer together with the irreducibility
property appropriate to the multiplicative ledger. -/
structure PrimeLedgerAtom (p : ℕ) : Prop where
  prime : Nat.Prime p
  irreduciblePosting : ∀ a b : ℕ, p = a * b → a = 1 ∨ b = 1

/-- Positive integers are the states of the multiplicative integer ledger. -/
def IntegerLedgerState (n : ℕ) : Prop := 0 < n

/-- A prime number is an irreducible posting of the integer ledger. -/
theorem prime_is_ledger_atom {p : ℕ} (hp : Nat.Prime p) : PrimeLedgerAtom p where
  prime := hp
  irreduciblePosting := by
    intro a b hab
    have ha_dvd : a ∣ p := ⟨b, by rw [hab]⟩
    have ha := hp.eq_one_or_self_of_dvd a ha_dvd
    rcases ha with ha | ha
    · exact Or.inl ha
    · right
      have hb_eq : p = p * b := by
        simpa [ha] using hab
      have hb : p * b = p * 1 := by
        simpa using hb_eq.symm
      exact Nat.mul_left_cancel hp.pos hb

/-- Ledger atoms are prime numbers. -/
theorem ledger_atom_is_prime {p : ℕ} (h : PrimeLedgerAtom p) : Nat.Prime p :=
  h.prime

/-- Prime-ledger atom iff ordinary primality. -/
theorem primeLedgerAtom_iff_prime (p : ℕ) :
    PrimeLedgerAtom p ↔ Nat.Prime p :=
  ⟨ledger_atom_is_prime, prime_is_ledger_atom⟩

/-- The unit is not a prime ledger atom. -/
theorem one_not_primeLedgerAtom : ¬ PrimeLedgerAtom 1 := by
  intro h
  exact Nat.not_prime_one h.prime

/-- Every prime is a positive ledger state. -/
theorem prime_is_positive_ledger_state {p : ℕ} (hp : Nat.Prime p) :
    IntegerLedgerState p := hp.pos

/-- Certificate for the arithmetic base of the prime ledger. -/
structure PrimeLedgerCert where
  atom_iff_prime : ∀ p : ℕ, PrimeLedgerAtom p ↔ Nat.Prime p
  one_not_atom : ¬ PrimeLedgerAtom 1
  prime_positive : ∀ {p : ℕ}, Nat.Prime p → IntegerLedgerState p

/-- The prime ledger certificate. -/
def primeLedgerCert : PrimeLedgerCert where
  atom_iff_prime := primeLedgerAtom_iff_prime
  one_not_atom := one_not_primeLedgerAtom
  prime_positive := prime_is_positive_ledger_state

end NumberTheory
end IndisputableMonolith

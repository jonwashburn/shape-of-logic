import Mathlib

/-!
# Finite Phase Completeness

The first phase-budget theorem: a non-identity integer ledger has a finite
cyclic quotient in which its phase is not the identity phase.

This is the finite arithmetic content behind the RS statement that a
non-identity reciprocal ledger cannot be invisible in all finite phase
quotients.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace FinitePhaseCompleteness

/-- A reciprocal integer ledger carrier. -/
structure ReciprocalIntegerLedger where
  carrier : ℕ
  carrier_pos : 0 < carrier
  nonidentity : carrier ≠ 1
  has_reciprocal_budget : ∃ N : ℕ, carrier ∣ N ^ 2

/-- Every reciprocal integer ledger has a finite cyclic phase quotient. -/
theorem finite_phase_completeness (L : ReciprocalIntegerLedger) :
    ∃ c : ℕ, 0 < c ∧ Nonempty (ZMod c) := by
  exact ⟨L.carrier, L.carrier_pos, ⟨0⟩⟩

/-- A non-identity positive integer is separated from the identity in a finite
cyclic quotient.  We use the quotient `Z/(carrier+1)Z`: the carrier has phase
`-1`, not `1`. -/
theorem finite_phase_separates_nonidentity (L : ReciprocalIntegerLedger) :
    ∃ c : ℕ, 0 < c ∧ (L.carrier : ZMod c) ≠ 1 := by
  refine ⟨L.carrier + 1, Nat.succ_pos L.carrier, ?_⟩
  intro h
  have hmod := (ZMod.natCast_eq_natCast_iff' L.carrier 1 (L.carrier + 1)).mp h
  have hleft : L.carrier % (L.carrier + 1) = L.carrier :=
    Nat.mod_eq_of_lt (Nat.lt_succ_self L.carrier)
  have hright : 1 % (L.carrier + 1) = 1 := by
    apply Nat.mod_eq_of_lt
    exact Nat.succ_lt_succ L.carrier_pos
  rw [hleft, hright] at hmod
  exact L.nonidentity hmod

end FinitePhaseCompleteness
end NumberTheory
end IndisputableMonolith

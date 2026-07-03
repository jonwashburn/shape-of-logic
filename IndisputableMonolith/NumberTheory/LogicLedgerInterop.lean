import Mathlib
import IndisputableMonolith.Foundation.IntegersFromLogic
import IndisputableMonolith.NumberTheory.FinitePhaseCompleteness

/-!
# Logic Ledger Interop

Transfers the recovered `LogicInt` ledger to the existing integer-ledger
phase-budget surface.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace LogicLedgerInterop

open FinitePhaseCompleteness

abbrev LogicInt := Foundation.IntegersFromLogic.LogicInt
abbrev logicIntToInt : LogicInt → Int := Foundation.IntegersFromLogic.LogicInt.toInt

/-- A recovered integer ledger is non-identity when its `Int` recovery is
positive and not equal to one. -/
structure LogicIntNonIdentityReciprocal (z : LogicInt) : Prop where
  pos : 0 < logicIntToInt z
  nonidentity : logicIntToInt z ≠ 1
  reciprocal_budget : ∃ N : ℕ, 0 < N ∧ Int.natAbs (logicIntToInt z) ∣ N ^ 2

/-- Positive recovered integers yield positive natural carriers. -/
theorem natAbs_pos_of_logicInt_pos
    {z : LogicInt}
    (hz : 0 < logicIntToInt z) :
    0 < Int.natAbs (logicIntToInt z) := by
  exact Int.natAbs_pos.mpr (ne_of_gt hz)

/-- Convert a non-identity recovered integer ledger into the Nat-level
reciprocal ledger used by finite phase completeness. -/
def reciprocalIntegerLedger_of_logicInt
    {z : LogicInt}
    (h : LogicIntNonIdentityReciprocal z) :
    ReciprocalIntegerLedger where
  carrier := Int.natAbs (logicIntToInt z)
  carrier_pos := natAbs_pos_of_logicInt_pos h.pos
  nonidentity := by
    intro hcarrier
    have h_toInt_abs : Int.natAbs (logicIntToInt z) = 1 := hcarrier
    have h_toInt : logicIntToInt z = 1 := by
      have habs_cast : (Int.natAbs (logicIntToInt z) : Int) = 1 := by
        exact_mod_cast h_toInt_abs
      rw [Int.natAbs_of_nonneg (le_of_lt h.pos)] at habs_cast
      exact habs_cast
    exact h.nonidentity h_toInt
  has_reciprocal_budget := by
    rcases h.reciprocal_budget with ⟨N, _hNpos, hdiv⟩
    exact ⟨N, hdiv⟩

/-- Recovered non-identity integer ledgers have a finite phase separating
them from identity. -/
theorem logicInt_finite_phase_separates
    {z : LogicInt}
    (h : LogicIntNonIdentityReciprocal z) :
    ∃ c : ℕ, 0 < c ∧
      ((reciprocalIntegerLedger_of_logicInt h).carrier : ZMod c) ≠ 1 :=
  finite_phase_separates_nonidentity (reciprocalIntegerLedger_of_logicInt h)

end LogicLedgerInterop
end NumberTheory
end IndisputableMonolith

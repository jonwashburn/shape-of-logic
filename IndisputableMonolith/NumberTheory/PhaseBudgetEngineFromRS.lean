import Mathlib
import IndisputableMonolith.NumberTheory.BoundedPhaseVisibility
import IndisputableMonolith.NumberTheory.PhaseBudgetToErdosStraus

/-!
# Phase Budget Engine from Recovered-Ledger Visibility

Turns the recovered-ledger bounded visibility engine into the phase-budget
engine already consumed by the Erdős-Straus residual proof chain.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace PhaseBudgetEngineFromRS

open BoundedPhaseVisibility
open PhaseBudgetToErdosStraus
open ErdosStrausRotationHierarchy

/-- Residual traps are positive nonidentity reciprocal ledgers. -/
def nonIdentityReciprocal_of_residualTrap {n : ℕ} (hn : ResidualTrap n) :
    NonIdentityReciprocal n where
  pos := Nat.zero_lt_of_lt hn.1
  nonidentity := by
    intro h
    have hlt : 1 < 1 := by simpa [h] using hn.1
    omega
  reciprocal_budget := by
    exact ⟨n, Nat.zero_lt_of_lt hn.1, by
      exact dvd_mul_right n n⟩

/-- A recovered-ledger bounded visibility engine supplies the phase-budget
engine needed by the Erdős-Straus chain. -/
def phaseBudgetEngine_of_boundedVisibilityEngine
    (engine : BoundedVisibilityEngine) :
    PhaseBudgetEngine where
  bound := engine.bound
  supplies_hit := by
    intro n hntrap
    exact engine.visibility n (nonIdentityReciprocal_of_residualTrap hntrap)

/-- Bounded visibility over recovered ledgers gives bounded balanced search. -/
def boundedBalancedSearch_of_boundedVisibilityEngine
    (engine : BoundedVisibilityEngine) :
    BoundedBalancedSearchEngine :=
  boundedBalancedSearch_of_phaseBudget
    (phaseBudgetEngine_of_boundedVisibilityEngine engine)

end PhaseBudgetEngineFromRS
end NumberTheory
end IndisputableMonolith

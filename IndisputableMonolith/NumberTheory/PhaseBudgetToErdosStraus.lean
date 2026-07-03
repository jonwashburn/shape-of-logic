import Mathlib
import IndisputableMonolith.NumberTheory.EffectivePrimePhaseInput
import IndisputableMonolith.NumberTheory.T1PhaseBudgetBound

/-!
# Phase Budget to Erdős-Straus

This module composes the phase-budget interface with the already-proved
Erdős-Straus RCL closure chain.

The result is conditional on a `PhaseBudgetEngine`: an explicit package saying
that the T1/RCL budget, uniform failure floor, and finite gate enumeration
produce a bounded subset-product phase hit for every residual trap.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace PhaseBudgetToErdosStraus

open ErdosStrausRotationHierarchy
open SubsetProductPhase
open PrimePhaseInput

/-- A phase-budget engine supplies the actual bounded subset-product hit.

The previous modules prove why such an engine is enough: finite phase
separation, finite failure-cost accumulation, and the T1/RCL stable-budget
interface.  This structure is the exact remaining physical bridge from those
budget facts to an explicit gate witness. -/
structure PhaseBudgetEngine where
  bound : ℕ → ℕ
  supplies_hit :
    ∀ n : ℕ, ResidualTrap n →
      ∃ c : ℕ, c ≤ bound n ∧ AdmissibleHardGate c ∧ Nonempty (SubsetProductPhaseHit n c)

/-- A phase-budget engine is exactly an effective prime phase input. -/
def effectivePrimePhaseInput_of_phaseBudgetEngine
    (engine : PhaseBudgetEngine) :
    EffectivePrimePhaseInput where
  bound := engine.bound
  supplies_generators := engine.supplies_hit

/-- A phase-budget engine supplies bounded balanced search. -/
def boundedBalancedSearch_of_phaseBudget
    (engine : PhaseBudgetEngine) :
    BoundedBalancedSearchEngine :=
  boundedBalancedSearch_of_effectivePrimePhaseInput
    (effectivePrimePhaseInput_of_phaseBudgetEngine engine)

/-- A phase-budget engine solves the residual trapped class. -/
theorem erdos_straus_residual_from_phaseBudget
    (engine : PhaseBudgetEngine)
    {n : ℕ} (hn : ResidualTrap n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  erdos_straus_residual_from_effectivePrimePhaseInput
    (effectivePrimePhaseInput_of_phaseBudgetEngine engine) hn

end PhaseBudgetToErdosStraus
end NumberTheory
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.NumberTheory.SubsetProductPhase
import IndisputableMonolith.NumberTheory.PrimePhaseDistribution

/-!
# Effective Prime Phase Input

This module states the exact prime-distribution input needed for the residual
Erdős-Straus proof and proves that it implies `PrimePhaseBoxDistribution`.

It deliberately avoids importing the currently bit-rotted
`PrimeDistributionBridge.lean`; that file is an upstream source candidate, not
a dependency of this interface.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace PrimePhaseInput

open ErdosStrausRotationHierarchy
open ErdosStrausBoxPhase
open SubsetProductPhase
open PrimePhaseDistribution

/-- Effective prime phase input: for every trapped ledger, bounded prime
phase supply produces an actual subset-product phase hit. -/
structure EffectivePrimePhaseInput where
  bound : ℕ → ℕ
  supplies_generators :
    ∀ n : ℕ, ResidualTrap n →
      ∃ c : ℕ, c ≤ bound n ∧ AdmissibleHardGate c ∧ Nonempty (SubsetProductPhaseHit n c)

/-- Effective prime phase supply gives the exact distribution statement
required by the residual Erdős-Straus chain. -/
def primePhaseBoxDistribution_of_effectivePrimePhaseInput
    (input : EffectivePrimePhaseInput) :
    PrimePhaseBoxDistribution where
  bound := input.bound
  hits := by
    intro n hn
    rcases input.supplies_generators n hn with ⟨c, hcbound, hc, ⟨hit⟩⟩
    exact ⟨c, hcbound, hc, generated_phase_hit_gives_HitsBalancedPhase hit⟩

/-- Effective prime phase supply gives bounded balanced search. -/
def boundedBalancedSearch_of_effectivePrimePhaseInput
    (input : EffectivePrimePhaseInput) :
    BoundedBalancedSearchEngine :=
  boundedBalancedSearch_of_primePhaseBoxDistribution
    (primePhaseBoxDistribution_of_effectivePrimePhaseInput input)

/-- Effective prime phase supply solves the residual trapped class. -/
theorem erdos_straus_residual_from_effectivePrimePhaseInput
    (input : EffectivePrimePhaseInput)
    {n : ℕ} (hn : ResidualTrap n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  erdos_straus_residual_from_prime_phase_box_distribution
    (primePhaseBoxDistribution_of_effectivePrimePhaseInput input) hn

/-- The intended RS source theorem.  This is the final remaining input:
derive `EffectivePrimePhaseInput` from the RCL prime-ledger machinery. -/
structure RSPrimePhaseEquidistribution where
  effective_input : EffectivePrimePhaseInput
  /-- Marker: this theorem is meant to be sourced from RCL/J-cost prime-ledger
  phase distribution, not from finite search. -/
  from_rcl_prime_ledger : True

def effectivePrimePhaseInput_of_rsPrimePhaseEquidistribution
    (rs : RSPrimePhaseEquidistribution) :
    EffectivePrimePhaseInput :=
  rs.effective_input

theorem erdos_straus_residual_from_rsPrimePhaseEquidistribution
    (rs : RSPrimePhaseEquidistribution)
    {n : ℕ} (hn : ResidualTrap n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  erdos_straus_residual_from_effectivePrimePhaseInput
    (effectivePrimePhaseInput_of_rsPrimePhaseEquidistribution rs) hn

end PrimePhaseInput
end NumberTheory
end IndisputableMonolith

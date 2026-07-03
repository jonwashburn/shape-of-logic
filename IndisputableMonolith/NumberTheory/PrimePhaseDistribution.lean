import Mathlib
import IndisputableMonolith.NumberTheory.ErdosStrausBoxPhase
import IndisputableMonolith.NumberTheory.PrimeCostSpectrum

/-!
# Prime Phase Distribution Interface for Erdős-Straus

The RCL algebra and finite square-budget closure are now theorem-grade.  The
global remaining step is a prime phase distribution theorem strong enough to
hit the required square-budget phase.

This module names that distribution statement exactly and proves that it
instantiates the existing `BoundedBalancedSearchEngine`.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace PrimePhaseDistribution

open ErdosStrausRotationHierarchy
open ErdosStrausBoxPhase

/-- Prime phase distribution over square-budget divisor boxes.

For every residual trapped `n`, a bounded admissible gate `c` has a divisor
box point hitting the required balanced phase. -/
structure PrimePhaseBoxDistribution where
  bound : ℕ → ℕ
  hits :
    ∀ n : ℕ, ResidualTrap n →
      ∃ c : ℕ, c ≤ bound n ∧ AdmissibleHardGate c ∧ HitsBalancedPhase n c

/-- The exact finite-combinatorial conversion:
prime phase box distribution gives the bounded balanced search engine. -/
def boundedBalancedSearch_of_primePhaseBoxDistribution
    (dist : PrimePhaseBoxDistribution) :
    BoundedBalancedSearchEngine where
  bound := dist.bound
  bound_ok := by
    intro n hn
    rcases dist.hits n hn with ⟨c, hcbound, hc, hhit⟩
    exact ⟨c, hcbound, hc, box_phase_hit_gives_balanced_pair hhit⟩

/-- If the prime phase box distribution theorem is supplied, the residual
Erdős-Straus class follows. -/
theorem erdos_straus_residual_from_prime_phase_box_distribution
    (dist : PrimePhaseBoxDistribution)
    {n : ℕ} (hn : ResidualTrap n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  bounded_balanced_search_solved
    (boundedBalancedSearch_of_primePhaseBoxDistribution dist) hn

/-! ## Existing RS prime-distribution surface

The imported prime modules currently provide:

* prime ledger cost additivity (`PrimeCostSpectrum`);
* an RH/frustration-spectrum bridge to aggregate prime distribution
  (`PrimeDistributionBridge`, currently an upstream repair target under
  the active Lean toolchain).

They do not yet prove the square-budget residue-box hit required above.
The following structure records the exact extra theorem needed from the
RS prime-distribution program. -/

/-- The missing first-principles bridge from the RS prime ledger to
Erdős-Straus square-budget phase hits. -/
structure RSPrimePhaseBoxTheorem : Type where
  distribution : PrimePhaseBoxDistribution
  /-- Marker that the theorem is intended to be derived from RCL/J-cost prime
  ledger machinery rather than inserted as an arithmetic oracle. -/
  from_rcl_prime_ledger : True

/-- Once the RS prime phase box theorem is derived, it supplies the desired
bounded balanced search engine. -/
def boundedBalancedSearch_of_rsPrimePhaseBoxTheorem
    (rs : RSPrimePhaseBoxTheorem) :
    BoundedBalancedSearchEngine :=
  boundedBalancedSearch_of_primePhaseBoxDistribution rs.distribution

/-- Final conditional form, with the remaining theorem named explicitly. -/
theorem erdos_straus_residual_from_rs_prime_phase_box
    (rs : RSPrimePhaseBoxTheorem)
    {n : ℕ} (hn : ResidualTrap n) :
    ErdosStrausRCL.HasRationalErdosStrausRepr (n : ℚ) :=
  bounded_balanced_search_solved
    (boundedBalancedSearch_of_rsPrimePhaseBoxTheorem rs) hn

end PrimePhaseDistribution
end NumberTheory
end IndisputableMonolith

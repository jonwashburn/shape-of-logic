import IndisputableMonolith.Information.CompressionPrior
import IndisputableMonolith.Information.EMLFromRecognition
import IndisputableMonolith.Information.FEPBridgeFromJCost
import IndisputableMonolith.Information.JCostNecessity
import IndisputableMonolith.Information.Thermodynamics

/-!
# Information Bridge Aggregator

This module aggregates the information-theoretic and thermodynamic
foundation of Recognition Science.

## Modules
- `CompressionPrior`: Minimum Description Length (MDL) grounded in J-cost.
- `EMLFromRecognition`: Oriented exp-log compiler gate from ledger coordinates.
- `FEPBridgeFromJCost`: Local FEP/KL contact with reciprocal J-cost.
- `JCostNecessity`: Proof of J-cost uniqueness from recognition axioms.
- `Thermodynamics`: Landauer limit and 8-tick dissipation.
-/

namespace IndisputableMonolith
namespace Information

/-- **HYPOTHESIS**: J-Cost Uniqueness.
    The J-cost is the unique symmetric minimal information cost.

    STATUS: SCAFFOLD — Proof established in `Information.JCostNecessity`.
    TODO: Fully unify the uniqueness theorem with the aggregator. -/
def H_UniquenessVerified : Prop :=
  ∀ (F : ℝ → ℝ), InformationCost F → (∀ x > 0, F x = Cost.Jcost x)

-- Legacy axiom eliminated. See CostUniqueness.T5_uniqueness_complete.

/-- **HYPOTHESIS**: Thermodynamic Bound.
    Recognition cost satisfies the Landauer bound for information erasure.

    STATUS: SCAFFOLD — Bound derived in `Information.Thermodynamics`.
    TODO: Complete the Taylor expansion proof in `Thermodynamics.lean`. -/
def H_ThermodynamicsVerified : Prop :=
  ∀ (s : Thermodynamics.LedgerState), ∀ b ∈ s.active_bonds,
    let m := s.bond_multipliers b
    let u := Real.log m
    Cost.Jcost m ≥ u^2 / 2

-- Legacy axiom eliminated. See Foundation.ConstantDerivations.

end Information
end IndisputableMonolith

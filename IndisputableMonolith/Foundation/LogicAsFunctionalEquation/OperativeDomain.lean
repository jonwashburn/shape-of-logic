import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.FiniteLogicalComparison

/-!
# Operative-domain identification

This module packages the formal chain:

finite logical comparison on positive ratios
  → encoded logical comparison
  → RCL family.

This is the Lean counterpart of the paper's operative-domain corollary.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- An operative-domain structure is finite logical comparison on the
continuous positive-ratio setting. -/
def OperativeDomainStructure (C : ComparisonOperator) : Prop :=
  FiniteLogicalComparison C

/-- Operative-domain structures satisfy the encoded laws of logic. -/
theorem operative_domain_satisfies_logic
    (C : ComparisonOperator)
    (hO : OperativeDomainStructure C) :
    SatisfiesLawsOfLogic C :=
  finite_logical_satisfies_laws C hO

/-- Operative-domain structures force the RCL family on the derived cost. -/
theorem operative_domain_identification
    (C : ComparisonOperator)
    (hO : OperativeDomainStructure C) :
    RCLFamily (derivedCost C) :=
  finite_logical_comparison_forces_rcl C hO

/-- Headline corollary: on the operative domain, logical comparison and the
RCL family have the same forced algebraic form. -/
theorem rcl_logic_reality_chain
    (C : ComparisonOperator)
    (hO : OperativeDomainStructure C) :
    SatisfiesLawsOfLogic C ∧ RCLFamily (derivedCost C) := by
  exact ⟨operative_domain_satisfies_logic C hO,
    operative_domain_identification C hO⟩

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

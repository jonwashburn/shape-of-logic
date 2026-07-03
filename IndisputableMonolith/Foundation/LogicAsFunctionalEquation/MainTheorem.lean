import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.PositiveRatioForcing
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.NoHiddenState
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.OperativeDomain

/-!
# Main theorem package for logic as functional equation

This module collects the formal chain closest to the paper's headline:

* scale-free comparison factors through positive ratios;
* no-hidden-state finite comparison gives counted-once composition;
* counted-once finite logical comparison forces the RCL family.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- No-hidden-state operative comparison forces the RCL family. -/
theorem no_hidden_state_logic_forces_rcl
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C)
    (hNoHidden : NoHiddenStateComposition C) :
    RCLFamily (derivedCost C) :=
  no_hidden_state_comparison_forces_rcl C hOp hNoHidden

/-- Counted-once finite logical comparison on positive ratios is RCL algebra. -/
theorem rcl_is_counted_once_logic_on_positive_ratios
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    RCLFamily (derivedCost C) :=
  finite_logical_comparison_forces_rcl C h

/-- The operative-domain chain: encoded logic plus RCL family. -/
theorem operative_domain_rcl_logic_reality_chain
    (C : ComparisonOperator)
    (h : OperativeDomainStructure C) :
    SatisfiesLawsOfLogic C ∧ RCLFamily (derivedCost C) :=
  rcl_logic_reality_chain C h

/-- Scale-free counted-once logical comparison factors through ratios and
then forces RCL on the derived cost. -/
theorem scale_free_counted_once_logic_forces_ratio_rcl
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    (∃ F : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → C x y = F (x / y)) ∧
    RCLFamily (derivedCost C) := by
  exact ⟨scale_free_comparison_factors_through_ratio C h.scale_invariant,
    finite_logical_comparison_forces_rcl C h⟩

/-- Final theorem-name alias: RCL is scale-free counted-once logic on positive
ratios. -/
theorem rcl_is_scale_free_counted_once_logic_on_positive_ratios
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    (∃ F : ℝ → ℝ, ∀ x y : ℝ, 0 < x → 0 < y → C x y = F (x / y)) ∧
    RCLFamily (derivedCost C) :=
  scale_free_counted_once_logic_forces_ratio_rcl C h

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

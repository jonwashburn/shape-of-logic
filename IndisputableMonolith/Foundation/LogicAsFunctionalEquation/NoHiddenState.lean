import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.LinearLogicBridge

/-!
# No-hidden-state comparison composition

No-hidden-state composition means the composite cost is supplied by a
counted-once resource expression in the two constituent costs.  This is a
formal version of "no hidden route memory, no branch choice, no infinite
series, and no reuse of a constituent comparison."
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- A no-hidden-state composition law for `C`: there is a counted-once resource
expression whose evaluation on the two constituent costs gives the composite
cost. -/
structure NoHiddenStateComposition (C : ComparisonOperator) where
  expr : CountedOnceResourceExpr
  symmetric_expr : ∀ u v, CountedOnceResourceExpr.eval expr u v =
    CountedOnceResourceExpr.eval expr v u
  composition : ∀ x y : ℝ, 0 < x → 0 < y →
    derivedCost C (x * y) + derivedCost C (x / y) =
      CountedOnceResourceExpr.eval expr (derivedCost C x) (derivedCost C y)

/-- No-hidden-state composition implies counted-once composition. -/
theorem no_hidden_state_implies_counted_once
    (C : ComparisonOperator)
    (h : NoHiddenStateComposition C) :
    CountedOnceComposition C := by
  refine ⟨fun u v => CountedOnceResourceExpr.eval h.expr u v, ?_, ?_, ?_⟩
  · exact CountedOnceResourceExpr.expr_induces_counted_once_combiner h.expr
  · exact h.symmetric_expr
  · exact h.composition

/-- A no-hidden-state operative comparison forces the RCL family. -/
theorem no_hidden_state_comparison_forces_rcl
    (C : ComparisonOperator)
    (hOp : OperativePositiveRatioComparison C)
    (h : NoHiddenStateComposition C) :
    RCLFamily (derivedCost C) :=
  counted_once_combiner_forces_rcl C hOp
    (no_hidden_state_implies_counted_once C h)

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.CountOnceComparison
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.RealityStructure

/-!
# Finite logical comparison

This module packages the paper's sharpened theorem:

finite logical comparison on positive ratios forces the RCL family.

The finite-pairwise-polynomial condition is not removed; it is named as the
finite algebraic content of logical comparison.  The counterexamples prove why
that finite condition is necessary.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

open IndisputableMonolith.Foundation.DAlembert.Inevitability

/-- A finite logical comparison is a truth-evaluable positive-ratio comparison
whose composite value is determined by a finite pairwise polynomial algebra. -/
structure FiniteLogicalComparison (C : ComparisonOperator) : Prop where
  identity : Identity C
  non_contradiction : NonContradiction C
  totality : ExcludedMiddle C
  scale_invariant : ScaleInvariant C
  nontrivial : NonTrivial C
  counted_once_algebra : CountedOnceComposition C

/-- Finite logical comparison supports truth-evaluable comparison. -/
theorem finite_logical_to_truth_evaluable
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    TruthEvaluableComparison C where
  self_evaluable := h.identity
  reorder_single_valued := h.non_contradiction
  determinate_continuous := h.totality
  composite_determinate := counted_once_to_finite_pairwise_polynomial C h.counted_once_algebra
  scale_free := h.scale_invariant
  nontrivial := h.nontrivial

/-- Finite logical comparison is operative positive-ratio comparison. -/
theorem finite_logical_to_operative
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    OperativePositiveRatioComparison C where
  identity := h.identity
  non_contradiction := h.non_contradiction
  continuous := h.totality
  scale_invariant := h.scale_invariant
  non_trivial := h.nontrivial

/-- Finite logical comparison carries finite pairwise polynomial closure. -/
theorem finite_logical_has_finite_closure
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    FinitePairwisePolynomialClosure C :=
  counted_once_to_finite_pairwise_polynomial C h.counted_once_algebra

/-- Finite logical comparison carries counted-once composition. -/
theorem finite_logical_has_counted_once
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    CountedOnceComposition C :=
  h.counted_once_algebra

/-- Finite logical comparison satisfies the encoded laws of logic. -/
theorem finite_logical_satisfies_laws
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    SatisfiesLawsOfLogic C :=
  operative_to_laws_of_logic C
    (finite_logical_to_operative C h)
    (finite_logical_has_finite_closure C h)

/-- Finite logical comparison on positive ratios forces the RCL family. -/
theorem finite_logical_comparison_forces_rcl
    (C : ComparisonOperator)
    (h : FiniteLogicalComparison C) :
    RCLFamily (derivedCost C) :=
  counted_once_combiner_forces_rcl C
    (finite_logical_to_operative C h)
    (finite_logical_has_counted_once C h)

/-- Searchable boundary theorem: arbitrary continuous composition is not enough
to force the RCL family. -/
theorem continuous_composition_not_enough :
    ¬ ∃ c : ℝ, ∀ a b : ℝ, 0 < a → 0 < b →
      quarticCombiner a b = 2 * a + 2 * b + c * a * b :=
  quarticCombiner_not_rcl_family

/-- Searchable boundary theorem: analytic composition is not enough to force
degree-two RCL form. -/
theorem analytic_composition_not_enough :
    ¬ ∃ c : ℝ, ∀ s : ℝ, reparamDiagonal s = degreeTwoDiagonal c s :=
  reparam_diagonal_not_degree_two

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

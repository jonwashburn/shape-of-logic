import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.Canonicality

/-!
# Truth-evaluable reality structures

This module formalises the "Reality ⇒ Logic" leg used by the Logic Functional
Equation paper.  The starting point is a comparison operator whose values are
truth-evaluable: self-comparison has a trivial value, reordering is
single-valued, every positive pair has a determinate continuous comparison,
and composite comparisons have a determinate finite pairwise combiner.

Lean verifies the object-level implication from truth-evaluability to the
encoded logical conditions (L1)--(L4).
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- A truth-evaluable comparison is the minimal structure needed to evaluate
statements about positive-ratio comparisons.  The four fields are stated in
semantic language; the lemmas below translate them into (L1)--(L4). -/
structure TruthEvaluableComparison (C : ComparisonOperator) : Prop where
  self_evaluable : ∀ x : ℝ, 0 < x → C x x = 0
  reorder_single_valued : ∀ x y : ℝ, 0 < x → 0 < y → C x y = C y x
  determinate_continuous :
    ContinuousOn (Function.uncurry C) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
  composite_determinate : FinitePairwisePolynomialClosure C
  scale_free : ScaleInvariant C
  nontrivial : NonTrivial C

/-- Truth-evaluability of self-statements gives identity. -/
theorem truth_eval_implies_identity
    (C : ComparisonOperator)
    (hT : TruthEvaluableComparison C) :
    Identity C :=
  hT.self_evaluable

/-- Truth-evaluability of reordered pair-statements gives non-contradiction. -/
theorem truth_eval_implies_non_contradiction
    (C : ComparisonOperator)
    (hT : TruthEvaluableComparison C) :
    NonContradiction C :=
  hT.reorder_single_valued

/-- Truth-evaluability of every positive pair gives totality/continuity on the
open positive quadrant. -/
theorem truth_eval_implies_totality
    (C : ComparisonOperator)
    (hT : TruthEvaluableComparison C) :
    ExcludedMiddle C :=
  hT.determinate_continuous

/-- Truth-evaluability of composite comparison-statements gives finite pairwise
composition. -/
theorem truth_eval_implies_composition
    (C : ComparisonOperator)
    (hT : TruthEvaluableComparison C) :
    FinitePairwisePolynomialClosure C :=
  hT.composite_determinate

/-- Truth-evaluable comparisons are operative positive-ratio comparisons. -/
theorem truth_eval_to_operative
    (C : ComparisonOperator)
    (hT : TruthEvaluableComparison C) :
    OperativePositiveRatioComparison C where
  identity := truth_eval_implies_identity C hT
  non_contradiction := truth_eval_implies_non_contradiction C hT
  continuous := truth_eval_implies_totality C hT
  scale_invariant := hT.scale_free
  non_trivial := hT.nontrivial

/-- Truth-evaluable comparisons satisfy the encoded laws of logic. -/
theorem reality_satisfies_logic
    (C : ComparisonOperator)
    (hT : TruthEvaluableComparison C) :
    SatisfiesLawsOfLogic C :=
  operative_to_laws_of_logic C
    (truth_eval_to_operative C hT)
    (truth_eval_implies_composition C hT)

/-- Consequently, truth-evaluable finite pairwise positive-ratio comparison
forces the RCL family. -/
theorem rcl_from_truth_evaluable_comparison
    (C : ComparisonOperator)
    (hT : TruthEvaluableComparison C) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      DAlembert.Inevitability.HasMultiplicativeConsistency (derivedCost C) P ∧
      (∀ u v, P u v = 2 * u + 2 * v + c * u * v) :=
  rcl_polynomial_closure_theorem C
    (truth_eval_to_operative C hT)
    (truth_eval_implies_composition C hT)

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

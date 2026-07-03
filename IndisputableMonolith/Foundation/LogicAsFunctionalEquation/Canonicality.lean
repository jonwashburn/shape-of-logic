import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.DirectProof

/-!
# Canonicality of the logic encoding

This module formalises the paper's canonicality step at the level Lean can
check: once a comparison operator is read as a magnitude of mismatch, the
operator-level conditions used in `LogicAsFunctionalEquation` are the
canonical structural content of that reading.

Lean verifies the implication from the magnitude-of-mismatch package to the
encoded logical conditions.  The philosophical claim that this package is the
right reading of Aristotle is documented in the paper, not proved by Lean.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- The magnitude-of-mismatch interpretation of a comparison operator.

The fields correspond to:
* trivial value at match,
* symmetry of the unordered pair,
* total/continuous determinability,
* scale-free comparison,
* nontriviality.

Finite pairwise polynomial closure is kept separate: it is not part of the
interpretation itself, but the finite-algebra condition needed to force RCL. -/
structure MagnitudeOfMismatch (C : ComparisonOperator) : Prop where
  trivial_at_match : Identity C
  pair_symmetric : NonContradiction C
  determinate_continuous : ExcludedMiddle C
  scale_free : ScaleInvariant C
  nontrivial : NonTrivial C

/-- The magnitude-of-mismatch interpretation determines the operative
positive-ratio comparison structure. -/
theorem mismatch_to_operative
    (C : ComparisonOperator)
    (hM : MagnitudeOfMismatch C) :
    OperativePositiveRatioComparison C where
  identity := hM.trivial_at_match
  non_contradiction := hM.pair_symmetric
  continuous := hM.determinate_continuous
  scale_invariant := hM.scale_free
  non_trivial := hM.nontrivial

/-- Under the magnitude-of-mismatch interpretation, identity is exactly the
zero self-cost condition used in the logic encoding. -/
theorem canonical_identity
    (C : ComparisonOperator)
    (hM : MagnitudeOfMismatch C) :
    Identity C :=
  hM.trivial_at_match

/-- Under the magnitude-of-mismatch interpretation, non-contradiction is
encoded as symmetric single-valued comparison. -/
theorem canonical_non_contradiction
    (C : ComparisonOperator)
    (hM : MagnitudeOfMismatch C) :
    NonContradiction C :=
  hM.pair_symmetric

/-- Under the magnitude-of-mismatch interpretation, excluded middle on the
continuous positive quadrant is encoded as determinate continuous comparison. -/
theorem canonical_excluded_middle
    (C : ComparisonOperator)
    (hM : MagnitudeOfMismatch C) :
    ExcludedMiddle C :=
  hM.determinate_continuous

/-- Under the magnitude-of-mismatch interpretation, the scale-free character
of logical comparison gives the scale-invariance bridge. -/
theorem canonical_scale_invariance
    (C : ComparisonOperator)
    (hM : MagnitudeOfMismatch C) :
    ScaleInvariant C :=
  hM.scale_free

/-- The canonical encoding, packaged: a magnitude-of-mismatch comparison plus
finite pairwise polynomial closure satisfies the Level-1 `SatisfiesLawsOfLogic`
structure. -/
theorem canonicality_of_encoding
    (C : ComparisonOperator)
    (hM : MagnitudeOfMismatch C)
    (hFinite : FinitePairwisePolynomialClosure C) :
    SatisfiesLawsOfLogic C :=
  operative_to_laws_of_logic C (mismatch_to_operative C hM) hFinite

/-- The RCL family follows from the canonical magnitude-of-mismatch reading
plus finite pairwise polynomial closure. -/
theorem rcl_from_canonical_mismatch_encoding
    (C : ComparisonOperator)
    (hM : MagnitudeOfMismatch C)
    (hFinite : FinitePairwisePolynomialClosure C) :
    ∃ (P : ℝ → ℝ → ℝ) (c : ℝ),
      DAlembert.Inevitability.HasMultiplicativeConsistency (derivedCost C) P ∧
      (∀ u v, P u v = 2 * u + 2 * v + c * u * v) :=
  rcl_polynomial_closure_theorem C (mismatch_to_operative C hM) hFinite

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

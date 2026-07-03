import IndisputableMonolith.Foundation.UniversalForcing.ContinuousRealization
import IndisputableMonolith.Foundation.UniversalForcing.DiscreteRealization

/-!
  TwoCases.lean

  First non-trivial invariance kernel: continuous positive-ratio realizations
  and the discrete Boolean realization have canonically equivalent forced
  arithmetic.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Invariance
namespace TwoCases

open LogicAsFunctionalEquation
open ContinuousRealization
open DiscreteRealization

/-- Continuous positive-ratio arithmetic is canonically equivalent to discrete
Boolean arithmetic. -/
noncomputable def arith_continuous_equiv_arith_discrete
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    (arithmeticOf (continuousRealization C h)).peano.carrier
      ≃ (arithmeticOf discreteRealization).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf (continuousRealization C h))
    (arithmeticOf discreteRealization)

end TwoCases
end Invariance
end UniversalForcing
end Foundation
end IndisputableMonolith

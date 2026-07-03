import IndisputableMonolith.Foundation.UniversalForcing

/-!
  ContinuousRealization.lean

  The continuous positive-ratio realization is the already-existing
  `LogicRealization.ofPositiveRatioComparison` wrapper, re-exported under the
  Universal Forcing namespace used by the program paper.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace ContinuousRealization

open LogicAsFunctionalEquation

/-- Continuous positive-ratio Law-of-Logic realization. -/
noncomputable def continuousRealization
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    LogicRealization :=
  LogicRealization.ofPositiveRatioComparison C h

/-- The continuous realization carries the universal forced arithmetic. -/
noncomputable def continuous_arith_equiv_logicNat
    (C : ComparisonOperator) (h : SatisfiesLawsOfLogic C) :
    (arithmeticOf (continuousRealization C h)).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  (continuousRealization C h).orbitEquivLogicNat

end ContinuousRealization
end UniversalForcing
end Foundation
end IndisputableMonolith

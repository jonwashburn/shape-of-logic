import IndisputableMonolith.Foundation.DiscreteLogicRealization

/-!
  DiscreteRealization.lean

  Re-export of the Boolean/propositional realization under the
  `Foundation.UniversalForcing` module tree.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace DiscreteRealization

open DiscreteLogicRealization

/-- Boolean/propositional Law-of-Logic realization. -/
def discreteRealization : LogicRealization :=
  boolRealization

/-- The discrete realization carries the universal forced arithmetic. -/
noncomputable def discrete_arith_equiv_logicNat :
    (arithmeticOf discreteRealization).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  discreteRealization.orbitEquivLogicNat

end DiscreteRealization
end UniversalForcing
end Foundation
end IndisputableMonolith

import IndisputableMonolith.Foundation.CategoricalLogicRealization

/-!
  CategoricalRealization.lean

  Re-export of the canonical categorical/Lawvere-style realization under the
  `Foundation.UniversalForcing` module tree.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace CategoricalRealization

open CategoricalLogicRealization

/-- Canonical categorical realization via the `LogicNat` Peano object. -/
def categoricalRealization : LogicRealization :=
  canonicalCategoricalRealization

/-- Categorical realization carries the universal forced arithmetic. -/
noncomputable def categorical_arith_equiv_logicNat :
    (arithmeticOf categoricalRealization).peano.carrier
      ≃ ArithmeticFromLogic.LogicNat :=
  categoricalRealization.orbitEquivLogicNat

end CategoricalRealization
end UniversalForcing
end Foundation
end IndisputableMonolith

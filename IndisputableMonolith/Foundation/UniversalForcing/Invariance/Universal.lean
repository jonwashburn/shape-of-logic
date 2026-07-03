import IndisputableMonolith.Foundation.UniversalForcing.Invariance.TwoCases
import IndisputableMonolith.Foundation.UniversalForcing.ModularRealization
import IndisputableMonolith.Foundation.UniversalForcing.OrderRealization
import IndisputableMonolith.Foundation.UniversalForcing.CategoricalRealization

/-!
  Universal.lean

  General Universal Forcing theorem: every Law-of-Logic realization carries
  canonically equivalent forced arithmetic.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Invariance
namespace Universal

/-- Every realization's forced arithmetic is canonically equivalent to the
reference `LogicNat` Peano object. -/
noncomputable def arith_universal_initial' (R : LogicRealization) :
    (arithmeticOf R).peano.carrier ≃ ArithmeticFromLogic.LogicNat :=
  R.orbitEquivLogicNat

/-- **Universal Forcing Meta-Theorem.**

For any two Law-of-Logic realizations, the forced arithmetic objects are
canonically equivalent. -/
noncomputable def universal_forcing (R S : LogicRealization) :
    (arithmeticOf R).peano.carrier ≃ (arithmeticOf S).peano.carrier :=
  ArithmeticOf.equivOfInitial (arithmeticOf R) (arithmeticOf S)

/-- Peano surface is available for every realization's forced arithmetic. -/
theorem universal_peano_surface (R : LogicRealization) :
    ArithmeticOf.PeanoSurface (arithmeticOf R) :=
  peano_surface R

end Universal
end Invariance
end UniversalForcing
end Foundation
end IndisputableMonolith

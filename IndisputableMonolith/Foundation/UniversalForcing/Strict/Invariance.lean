import IndisputableMonolith.Foundation.UniversalForcing.Strict.Categorical

/-!
  Strict/Invariance.lean

  Strict Universal Forcing theorem: native Law-of-Logic data determines a
  derived free orbit, and all derived free orbits are canonically equivalent.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace Invariance

/-- Every strict realization's derived forced arithmetic is canonically
equivalent to `LogicNat`. -/
def strict_arith_universal_initial (R : StrictLogicRealization) :
    (StrictLogicRealization.arith R).peano.carrier ≃ ArithmeticFromLogic.LogicNat :=
  (StrictLogicRealization.toLightweight R).orbitEquivLogicNat

/-- **Strict Universal Forcing.**

For any two strict Law-of-Logic realizations, the arithmetic derived from
their native law data is canonically equivalent. -/
noncomputable def strict_universal_forcing (R S : StrictLogicRealization) :
    (StrictLogicRealization.arith R).peano.carrier
      ≃ (StrictLogicRealization.arith S).peano.carrier :=
  ArithmeticOf.equivOfInitial (StrictLogicRealization.arith R)
    (StrictLogicRealization.arith S)

/-- The Peano surface for every strict realization. -/
theorem strict_peano_surface (R : StrictLogicRealization) :
    ArithmeticOf.PeanoSurface (StrictLogicRealization.arith R) :=
  StrictLogicRealization.peano_surface R

end Invariance
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith

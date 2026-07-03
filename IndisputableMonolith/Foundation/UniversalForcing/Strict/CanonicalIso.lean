import IndisputableMonolith.Foundation.UniversalForcing.Strict.Invariance
import IndisputableMonolith.Foundation.UniversalForcing.CanonicalIso

/-!
  Strict/CanonicalIso.lean

  Structure-preserving Universal Forcing for the strict "no escape hatch"
  realizations.

  `Strict/Invariance.lean` already proves the strict universal forcing bijection
  `strict_universal_forcing R S` between the forced arithmetics of any two
  `StrictLogicRealization`s.  This module upgrades that bijection, on the strict
  surface, to a *unique structure-preserving isomorphism* of Peano algebras,
  reusing `UniversalForcing.universalForcingPeanoEquiv` and
  `UniversalForcing.peanoEquiv_unique` through the strict-to-lightweight functor.

  A strict realization supplies only native comparison / composition / identity /
  invariance / non-triviality data; its forced arithmetic is derived, not
  supplied.  So the canonical Peano isomorphism here is genuinely forced by the
  native law data, with no orbit handed in by the caller.
-/

namespace IndisputableMonolith
namespace Foundation
namespace UniversalForcing
namespace Strict
namespace CanonicalIso

/-- **Strict Universal Forcing, structure-preserving form.**

For any two strict Law-of-Logic realizations, the bijection between their forced
arithmetics is a structure-preserving isomorphism of Peano algebras: it sends
zero to zero and commutes with the successor map. -/
noncomputable def strict_universal_forcing_peanoEquiv
    (R S : StrictLogicRealization) :
    PeanoEquiv (StrictLogicRealization.arith R).peano
      (StrictLogicRealization.arith S).peano :=
  universalForcingPeanoEquiv (StrictLogicRealization.toLightweight R)
    (StrictLogicRealization.toLightweight S)

/-- **Strict canonicality.**

Any two structure-preserving isomorphisms between the forced arithmetics of two
strict realizations have the same underlying function.  The strict universal
forcing isomorphism is therefore the unique one. -/
theorem strict_peanoEquiv_unique (R S : StrictLogicRealization)
    (e₁ e₂ : PeanoEquiv (StrictLogicRealization.arith R).peano
      (StrictLogicRealization.arith S).peano) :
    (e₁.toEquiv : (StrictLogicRealization.arith R).peano.carrier
        → (StrictLogicRealization.arith S).peano.carrier)
      = e₂.toEquiv :=
  peanoEquiv_unique (StrictLogicRealization.toLightweight R)
    (StrictLogicRealization.toLightweight S) e₁ e₂

/-- **Strict Universal Forcing isomorphism certificate.**

For any two strict Law-of-Logic realizations there is a canonical
structure-preserving isomorphism between their forced arithmetics, and it is
unique. -/
structure StrictUniversalForcingIsoCert where
  /-- The canonical Peano-algebra isomorphism between any two strict forced
  arithmetics. -/
  iso : ∀ R S : StrictLogicRealization,
    PeanoEquiv (StrictLogicRealization.arith R).peano
      (StrictLogicRealization.arith S).peano
  /-- That isomorphism is unique as a structure-preserving map. -/
  unique : ∀ (R S : StrictLogicRealization)
      (e₁ e₂ : PeanoEquiv (StrictLogicRealization.arith R).peano
        (StrictLogicRealization.arith S).peano),
      (e₁.toEquiv : (StrictLogicRealization.arith R).peano.carrier
          → (StrictLogicRealization.arith S).peano.carrier)
        = e₂.toEquiv

/-- The strict certificate is inhabited by the strict canonical iso and its
uniqueness. -/
noncomputable def strictUniversalForcingIsoCert : StrictUniversalForcingIsoCert where
  iso := fun R S => strict_universal_forcing_peanoEquiv R S
  unique := fun R S => strict_peanoEquiv_unique R S

end CanonicalIso
end Strict
end UniversalForcing
end Foundation
end IndisputableMonolith

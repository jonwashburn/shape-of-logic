import IndisputableMonolith.Foundation.MaximalForcing.AdmissibleRealization

/-!
# Maximal Forcing: Closure Operator

`ForcingClosure` is the claim set currently targeted by a primitive in a chosen
universe of realizations. The program is complete only when every claim in the
closure is classified as forced, independent, or selected with a named principle
that is itself scheduled for tightening.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

universe u

/-- A universe of realizations and claims for one maximal-forcing pass. -/
structure ClaimUniverse where
  Realization : Type u
  admissibility : AdmissibilityClass Realization
  claims : Set (RealityClaim Realization)

/-- Closure operator: for a primitive and a claim universe, return the claims
whose status is being closed. Later phases will make this operator constructive
from syntax / semantics; here it is the execution interface. -/
def ForcingClosure (_P : Primitive) (U : ClaimUniverse.{u}) :
    Set (RealityClaim U.Realization) :=
  U.claims

/-- A claim is in scope for maximal closure from a primitive. -/
def InClosure (P : Primitive) (U : ClaimUniverse.{u})
    (C : RealityClaim U.Realization) : Prop :=
  C ∈ ForcingClosure P U

end MaximalForcing
end Foundation
end IndisputableMonolith

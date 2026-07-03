import IndisputableMonolith.Foundation.MaximalForcing.IndependenceWitness

/-!
# Maximal Forcing: Claim Classification

Every claim in a closure target must eventually be classified as forced,
independent, or selected. `Selected` is an honest temporary tag, not an endpoint:
it must either be promoted to `Forced` by a deeper admissibility condition or
demoted to `Independent` by countermodel.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

universe u

/-- Classification of one claim in one closure universe. -/
inductive ClaimClassification (U : ClaimUniverse.{u})
    (C : RealityClaim U.Realization) : Prop where
  /-- Holds in every admissible realization. -/
  | forced : Forced U.admissibility.admissible C -> ClaimClassification U C
  /-- Two admissible realizations disagree on the claim. -/
  | independent : IndependenceWitness U C -> ClaimClassification U C
  /-- Not currently forced, but governed by a named selection principle. -/
  | selected : Selected U.admissibility.admissible C -> ClaimClassification U C

/-- A forced invariant is a closure claim with a proof of forcedness. -/
structure ForcedInvariant (P : Primitive) (U : ClaimUniverse.{u}) where
  claim : RealityClaim U.Realization
  in_closure : InClosure P U claim
  forced : Forced U.admissibility.admissible claim

end MaximalForcing
end Foundation
end IndisputableMonolith

import IndisputableMonolith.Foundation.MaximalForcing.ForcingClosure

/-!
# Maximal Forcing: Independence Witnesses

If a claim is not forced, maximal closure demands a countermodel pair rather
than a vague appeal to contingency.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

universe u

/-- Explicit countermodel pair for independence of a claim over an admissible
class. -/
structure IndependenceWitness (U : ClaimUniverse.{u})
    (C : RealityClaim U.Realization) where
  yes_model : U.Realization
  no_model : U.Realization
  yes_admissible : yes_model ∈ U.admissibility.admissible
  no_admissible : no_model ∈ U.admissibility.admissible
  yes_holds : C.holds yes_model
  no_fails : ¬ C.holds no_model

/-- An explicit witness implies the proposition-level `Independent` tag. -/
theorem independent_of_witness {U : ClaimUniverse.{u}}
    {C : RealityClaim U.Realization}
    (W : IndependenceWitness U C) :
    Independent U.admissibility.admissible C := by
  exact ⟨W.yes_model, W.no_model, W.yes_admissible, W.no_admissible,
    W.yes_holds, W.no_fails⟩

end MaximalForcing
end Foundation
end IndisputableMonolith

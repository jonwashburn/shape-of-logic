import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.RecogSpec.InevitabilityScaffold

namespace IndisputableMonolith
namespace RecogSpec

/-- Lightweight derivation of `Recognition_Closure` from the inevitability lemmas.

    The component predicates (`Inevitability_dimless`, `Inevitability_absolute`,
    and `Recognition_Closure`) are defined in `Spec.lean`.
-/
theorem recognition_closure_any (φ : ℝ) : Recognition_Closure φ := by
  have hDim : Inevitability_dimless φ := inevitability_dimless_holds φ
  have hAbs : Inevitability_absolute φ := inevitability_absolute_holds φ
  exact recognition_closure_from_inevitabilities (φ:=φ) hDim hAbs

end RecogSpec
end IndisputableMonolith

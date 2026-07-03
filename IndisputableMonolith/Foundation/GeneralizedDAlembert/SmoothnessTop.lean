import Mathlib

/-!
  Finite-to-top smoothness helper for the continuous-combiner d'Alembert
  route.

  Mathlib records `C^\infty` smoothness as `ContDiff 𝕜 ⊤ f`. The theorem
  `contDiff_infty` identifies this with `C^n` smoothness for every finite
  `n`. This file isolates that API step so the main generalized d'Alembert
  module does not carry it as an axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace GeneralizedDAlembert
namespace SmoothnessTop

theorem contDiff_top_of_contDiff_nat
    {f : ℝ → ℝ}
    (hFinite : ∀ n : ℕ, ContDiff ℝ n f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := by
  exact (contDiff_infty).2 hFinite

end SmoothnessTop
end GeneralizedDAlembert
end Foundation
end IndisputableMonolith

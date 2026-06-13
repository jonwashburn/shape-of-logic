import Mathlib

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real

/-! # AczelSmoothnessPackage Class

This module declares the typeclass interface for the d'Alembert smoothness
package and the bootstrap theorem that uses it. The class is a typeclass-style
hypothesis carrier; concrete instances live in
`IndisputableMonolith.Cost.AczelProof`.

History: pre-2026-04-25 the class was declared in the curated public-release
sibling `RecognitionScience/Cost/AczelTheorem.lean`. The 2026-04-25 RS↔IM
consolidation kept the larger IM `AczelTheorem.lean` (the unconditional proof)
and the larger RS `FunctionalEquation.lean` (the typeclass-parameterized
Law of Logic cost theorem). This split file decouples the class declaration
from both, so neither has to depend on the other.
-/

/-- Aczél smoothness requirement: continuous d'Alembert solutions are C^∞.

Any continuous solution of H(t+u) + H(t-u) = 2·H(t)·H(u) with H(0) = 1
is infinitely differentiable.

Mathematical basis (Aczél 1966, Ch. 3): the complete classification is
1. H(t) = 1 (constant, trivially C^∞)
2. H(t) = cosh(λt), λ ≠ 0 (C^∞)
3. H(t) = cos(λt), λ ≠ 0 (C^∞)

A concrete `instance` is provided in `IndisputableMonolith.Cost.AczelProof`
via the unconditional `dAlembert_contDiff_top` theorem in
`IndisputableMonolith.Cost.AczelTheorem`. -/
class AczelSmoothnessPackage : Prop where
  smooth_of_dAlembert :
    ∀ (H : ℝ → ℝ),
      H 0 = 1 →
      Continuous H →
      (∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) →
      ContDiff ℝ ⊤ H

/-- Smoothness of continuous d'Alembert solutions, parameterized by an
`AczelSmoothnessPackage` instance. -/
theorem aczel_dAlembert_smooth [AczelSmoothnessPackage] (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ContDiff ℝ ⊤ H :=
  AczelSmoothnessPackage.smooth_of_dAlembert H h_one h_cont h_dAlembert

end FunctionalEquation
end Cost
end IndisputableMonolith

import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Cost.AczelProof

open IndisputableMonolith

/-!
# Aczél-Based Closure for Functional Equation Uniqueness

This file isolates the legacy Aczél-dependent closure theorems from the
axiom-free core in `IndisputableMonolith.Cost.FunctionalEquation`.

The unconditional IM theorem surface should import the core module directly.
This compatibility module exists only for callers that still want the
one-line Aczél closure theorems.
-/

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real

/-! ## Thin Compatibility Surface

The helper lemmas that used to live here now live in
`IndisputableMonolith.Cost.FunctionalEquation`. This file remains only for
legacy imports that want a one-line Aczél closure theorem. -/

/-- **Law of Logic cost theorem, Aczél closure**: The J-cost function is the unique
    reciprocal cost satisfying the RCL, normalization, calibration, and continuity.

    This version uses the global Aczél axiom internally and requires NO regularity
    hypothesis parameters from the caller. -/
theorem law_of_logic_forces_jcost_aczel (F : ℝ → ℝ)
    (hRecip : IsReciprocalCost F)
    (hNorm : IsNormalized F)
    (hComp : SatisfiesCompositionLaw F)
    (hCalib : IsCalibrated F)
    (hCont : ContinuousOn F (Set.Ioi 0)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  exact law_of_logic_forces_jcost F hRecip hNorm hComp hCalib hCont

end FunctionalEquation
end Cost
end IndisputableMonolith

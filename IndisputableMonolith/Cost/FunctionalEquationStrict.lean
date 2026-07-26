import IndisputableMonolith.Cost.AczelProof
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Strict Functional-Equation Variants

This optional module tightens the T5 regularity surface without changing the
core theorem.  The theorem below replaces the explicit
`ContinuousOn F (Set.Ioi 0)` premise with limit-form log calibration.

History, 2026-07-25. Until that date this theorem was **vacuous**. Limit-form
calibration was stated on the full neighbourhood filter, which Lean's total
division makes unsatisfiable at `κ = 1`, so the premise it traded continuity for
was false and the trade bought nothing. `HasLogCurvature` is now punctured and
carries a non-vacuity witness (`jcost_hasLogCurvature_one`), so the statement has
content. It is also no longer the sharpest form: reciprocity, normalization, and
the derivative calibration are all redundant here, and
`composition_logCurvature_forces_jcost` states the result on the two premises
that do the work. This wrapper is kept for its callers.
-/

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real

/-- Limit-form log calibration supplies the continuity needed by the Aczél
d'Alembert route, so the explicit `ContinuousOn F (Set.Ioi 0)` premise can be
removed from this T5 variant.

Only `hComp` and `hLogCalib` are used: the other three premises are consequences
of that pair. They are retained so existing callers keep type-checking. -/
theorem law_of_logic_forces_jcost_of_log_calibration (F : ℝ → ℝ)
    [AczelSmoothnessPackage]
    (_hRecip : IsReciprocalCost F)
    (_hNorm : IsNormalized F)
    (hComp : SatisfiesCompositionLaw F)
    (_hCalib : IsCalibrated F)
    (hLogCalib : IsCalibratedLimit F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x :=
  composition_logCurvature_forces_jcost F hComp hLogCalib

/-- **The cost theorem on two premises, unconditionally.**

`composition_logCurvature_forces_jcost` is stated in `FunctionalEquation`, which
does not import the module that builds the `AczelSmoothnessPackage` instance, so
there it carries the package as an instance argument. This module does import it,
so here the theorem stands with no instance argument and no hypotheses beyond the
composition law and unit log curvature. Cite this one. -/
theorem composition_logCurvature_forces_jcost_unconditional (F : ℝ → ℝ)
    (hComp : SatisfiesCompositionLaw F)
    (hκ : HasLogCurvature (H F) 1) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x :=
  composition_logCurvature_forces_jcost F hComp hκ

end FunctionalEquation
end Cost
end IndisputableMonolith

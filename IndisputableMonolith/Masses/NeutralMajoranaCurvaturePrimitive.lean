import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaCurvatureRule

/-!
# Neutral Majorana curvature primitive

`NeutralMajoranaCurvatureRule` isolates the curvature scalar of the two-sheet
Majorana metric. This module names that scalar as the primitive neutral
curvature:

  `neutralMajoranaCurvaturePrimitive = majoranaCurvatureRule`.

The primitive is positive, below `0.021`, and recovers the observed neutral
splitting ratio through the realized-length rule.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaCurvaturePrimitive

open NeutralMajoranaCurvatureRule
open NeutralMajoranaTwoSheetMetricOperator
open NeutralMajoranaRealizedLengthRule
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Primitive neutral curvature scalar emitted by the two-sheet Majorana geometry. -/
def neutralMajoranaCurvaturePrimitive : ℝ :=
  majoranaCurvatureRule

theorem neutralMajoranaCurvaturePrimitive_eq_rule :
    neutralMajoranaCurvaturePrimitive = majoranaCurvatureRule := rfl

theorem neutralMajoranaCurvaturePrimitive_bounds :
    (0 : ℝ) < neutralMajoranaCurvaturePrimitive ∧
      neutralMajoranaCurvaturePrimitive < (0.021 : ℝ) := by
  unfold neutralMajoranaCurvaturePrimitive
  exact majoranaCurvatureRule_bounds

theorem majoranaRealizedLengthRule_eq_ambient_minus_primitive :
    majoranaRealizedLengthRule =
      majoranaTwoSheetMetricOperator.ambientLength * (1 - neutralMajoranaCurvaturePrimitive) := by
  unfold neutralMajoranaCurvaturePrimitive
  exact majoranaRealizedLengthRule_eq_ambient_minus_majorana_curvature

theorem neutralMajoranaCurvaturePrimitive_recovers_observed :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - neutralMajoranaCurvaturePrimitive)) *
        pureHalfLoopRatio = observedRatio := by
  unfold neutralMajoranaCurvaturePrimitive
  exact majoranaCurvatureRule_recovers_observed

/-- Certificate for the neutral Majorana curvature primitive. -/
structure NeutralMajoranaCurvaturePrimitiveCert where
  primitive_eq_rule : neutralMajoranaCurvaturePrimitive = majoranaCurvatureRule
  primitive_bounds :
    (0 : ℝ) < neutralMajoranaCurvaturePrimitive ∧
      neutralMajoranaCurvaturePrimitive < (0.021 : ℝ)
  realized_length_form :
    majoranaRealizedLengthRule =
      majoranaTwoSheetMetricOperator.ambientLength * (1 - neutralMajoranaCurvaturePrimitive)
  observed_recovered :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - neutralMajoranaCurvaturePrimitive)) *
        pureHalfLoopRatio = observedRatio

theorem neutralMajoranaCurvaturePrimitiveCert_holds :
    NeutralMajoranaCurvaturePrimitiveCert where
  primitive_eq_rule := neutralMajoranaCurvaturePrimitive_eq_rule
  primitive_bounds := neutralMajoranaCurvaturePrimitive_bounds
  realized_length_form := majoranaRealizedLengthRule_eq_ambient_minus_primitive
  observed_recovered := neutralMajoranaCurvaturePrimitive_recovers_observed

end

end NeutralMajoranaCurvaturePrimitive
end Masses
end IndisputableMonolith

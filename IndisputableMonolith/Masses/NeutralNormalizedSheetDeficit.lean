import Mathlib
import IndisputableMonolith.Masses.NeutralCurvatureFromSheetGeometry

/-!
# Neutral normalized sheet deficit

`NeutralCurvatureFromSheetGeometry` identifies neutral curvature with normalized
ambient-realized sheet deficit. This module names that deficit directly:

  `neutralNormalizedSheetDeficit = sheetGeometryCurvature`.

The deficit is the scalar still requiring a primitive sheet-count derivation. It
is positive, below `0.021`, equals the neutral Majorana curvature primitive, and
recovers the observed neutral splitting ratio through the two-sheet rule.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralNormalizedSheetDeficit

open NeutralCurvatureFromSheetGeometry
open NeutralMajoranaCurvaturePrimitive
open NeutralMajoranaTwoSheetMetricOperator
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Normalized ambient-realized deficit in the neutral two-sheet geometry. -/
def neutralNormalizedSheetDeficit : ℝ :=
  sheetGeometryCurvature

theorem neutralNormalizedSheetDeficit_eq_sheet :
    neutralNormalizedSheetDeficit = sheetGeometryCurvature := rfl

theorem neutralNormalizedSheetDeficit_eq_primitive :
    neutralNormalizedSheetDeficit = neutralMajoranaCurvaturePrimitive := by
  unfold neutralNormalizedSheetDeficit
  exact sheetGeometryCurvature_eq_primitive

theorem neutralNormalizedSheetDeficit_bounds :
    (0 : ℝ) < neutralNormalizedSheetDeficit ∧
      neutralNormalizedSheetDeficit < (0.021 : ℝ) := by
  unfold neutralNormalizedSheetDeficit
  exact sheetGeometryCurvature_bounds

theorem neutralNormalizedSheetDeficit_recovers_observed :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - neutralNormalizedSheetDeficit)) *
        pureHalfLoopRatio = observedRatio := by
  unfold neutralNormalizedSheetDeficit
  exact sheetGeometryCurvature_recovers_observed

/-- Certificate for the neutral normalized sheet deficit. -/
structure NeutralNormalizedSheetDeficitCert where
  deficit_eq_sheet : neutralNormalizedSheetDeficit = sheetGeometryCurvature
  deficit_eq_primitive : neutralNormalizedSheetDeficit = neutralMajoranaCurvaturePrimitive
  deficit_bounds :
    (0 : ℝ) < neutralNormalizedSheetDeficit ∧
      neutralNormalizedSheetDeficit < (0.021 : ℝ)
  observed_recovered :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - neutralNormalizedSheetDeficit)) *
        pureHalfLoopRatio = observedRatio

theorem neutralNormalizedSheetDeficitCert_holds :
    NeutralNormalizedSheetDeficitCert where
  deficit_eq_sheet := neutralNormalizedSheetDeficit_eq_sheet
  deficit_eq_primitive := neutralNormalizedSheetDeficit_eq_primitive
  deficit_bounds := neutralNormalizedSheetDeficit_bounds
  observed_recovered := neutralNormalizedSheetDeficit_recovers_observed

end

end NeutralNormalizedSheetDeficit
end Masses
end IndisputableMonolith

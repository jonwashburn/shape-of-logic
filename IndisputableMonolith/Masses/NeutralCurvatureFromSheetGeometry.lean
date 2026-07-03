import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaCurvaturePrimitive

/-!
# Neutral curvature from sheet geometry

`NeutralMajoranaCurvaturePrimitive` names the curvature scalar in the neutral
sector. This module sources it from the two-sheet geometry already present in
the Majorana metric: curvature is normalized ambient-realized sheet deficit.

The module proves the sheet-geometry curvature equals the primitive, remains in
`(0,0.021)`, and recovers the observed neutrino splitting ratio through the
two-sheet realized-length rule.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralCurvatureFromSheetGeometry

open NeutralMajoranaCurvaturePrimitive
open NeutralMajoranaCurvatureRule
open NeutralMajoranaTwoSheetMetricOperator
open NeutralCurvatureFromTwoSheetMetric
open NeutralMajoranaRealizedLengthRule
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Sheet-geometry curvature from normalized ambient-realized deficit. -/
def sheetGeometryCurvature : ℝ :=
  (majoranaTwoSheetMetricOperator.ambientLength - majoranaTwoSheetMetricOperator.realizedLength) /
    majoranaTwoSheetMetricOperator.ambientLength

theorem sheetGeometryCurvature_eq_metric :
    sheetGeometryCurvature = twoSheetMetricCurvature majoranaTwoSheetMetricOperator := by
  unfold sheetGeometryCurvature twoSheetMetricCurvature
  rfl

theorem sheetGeometryCurvature_eq_primitive :
    sheetGeometryCurvature = neutralMajoranaCurvaturePrimitive := by
  rw [sheetGeometryCurvature_eq_metric]
  unfold neutralMajoranaCurvaturePrimitive majoranaCurvatureRule
  rfl

theorem sheetGeometryCurvature_bounds :
    (0 : ℝ) < sheetGeometryCurvature ∧ sheetGeometryCurvature < (0.021 : ℝ) := by
  rw [sheetGeometryCurvature_eq_primitive]
  exact neutralMajoranaCurvaturePrimitive_bounds

theorem sheetGeometryCurvature_recovers_observed :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - sheetGeometryCurvature)) *
        pureHalfLoopRatio = observedRatio := by
  rw [sheetGeometryCurvature_eq_primitive]
  exact neutralMajoranaCurvaturePrimitive_recovers_observed

/-- Certificate for deriving neutral curvature from sheet geometry. -/
structure NeutralCurvatureFromSheetGeometryCert where
  curvature_eq_metric :
    sheetGeometryCurvature = twoSheetMetricCurvature majoranaTwoSheetMetricOperator
  curvature_eq_primitive :
    sheetGeometryCurvature = neutralMajoranaCurvaturePrimitive
  curvature_bounds :
    (0 : ℝ) < sheetGeometryCurvature ∧ sheetGeometryCurvature < (0.021 : ℝ)
  observed_recovered :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - sheetGeometryCurvature)) *
        pureHalfLoopRatio = observedRatio

theorem neutralCurvatureFromSheetGeometryCert_holds :
    NeutralCurvatureFromSheetGeometryCert where
  curvature_eq_metric := sheetGeometryCurvature_eq_metric
  curvature_eq_primitive := sheetGeometryCurvature_eq_primitive
  curvature_bounds := sheetGeometryCurvature_bounds
  observed_recovered := sheetGeometryCurvature_recovers_observed

end

end NeutralCurvatureFromSheetGeometry
end Masses
end IndisputableMonolith

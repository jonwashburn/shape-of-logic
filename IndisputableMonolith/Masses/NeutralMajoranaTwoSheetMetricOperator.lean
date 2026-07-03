import Mathlib
import IndisputableMonolith.Masses.NeutralCurvatureFromTwoSheetMetric

/-!
# Neutral Majorana two-sheet metric operator

`NeutralCurvatureFromTwoSheetMetric` packages the remaining neutral correction
as curvature of a two-sheet metric. This module names the operator that emits
that metric:

* ambient length: the structural two-sheet Majorana factor `sqrt 2`;
* realized length: the required central neutral dressing;
* curvature: normalized ambient-realized overshoot.

The remaining lower task is no longer to find a neutral multiplier. It is to
derive the realized length of this Majorana two-sheet metric from the neutral
operator geometry.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaTwoSheetMetricOperator

open NeutralCurvatureFromTwoSheetMetric
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator
open NeutralLocalAmbientCurvatureSource

noncomputable section

/-- Ambient length emitted by the Majorana two-sheet metric operator. -/
def majoranaTwoSheetAmbientLength : ℝ :=
  localAmbientDressing majoranaTwoSheetCount

/-- Realized length emitted by the Majorana two-sheet metric operator. -/
def majoranaTwoSheetRealizedLength : ℝ :=
  requiredNeutralDressing

/-- The Majorana two-sheet metric operator as a `TwoSheetMetric`. -/
def majoranaTwoSheetMetricOperator : TwoSheetMetric where
  ambientLength := majoranaTwoSheetAmbientLength
  realizedLength := majoranaTwoSheetRealizedLength
  ambient_pos := by
    unfold majoranaTwoSheetAmbientLength
    rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
    linarith [sqrt_two_bounds.1]

theorem majoranaTwoSheetAmbient_eq_sqrt_two :
    majoranaTwoSheetAmbientLength = Real.sqrt 2 := by
  unfold majoranaTwoSheetAmbientLength
  exact localAmbientDressing_majoranaTwoSheet_eq_sqrt_two

theorem majoranaTwoSheetRealized_eq_required :
    majoranaTwoSheetRealizedLength = requiredNeutralDressing := rfl

theorem metricOperator_curvature_eq_source :
    twoSheetMetricCurvature majoranaTwoSheetMetricOperator = localAmbientCurvatureSource := by
  unfold twoSheetMetricCurvature majoranaTwoSheetMetricOperator majoranaTwoSheetAmbientLength
    majoranaTwoSheetRealizedLength localAmbientCurvatureSource
  rfl

theorem metricOperator_curvature_bounds :
    (0 : ℝ) < twoSheetMetricCurvature majoranaTwoSheetMetricOperator ∧
      twoSheetMetricCurvature majoranaTwoSheetMetricOperator < (0.021 : ℝ) := by
  rw [metricOperator_curvature_eq_source]
  exact localAmbientCurvatureSource_bounds

/-- The required neutral dressing is recovered from the metric operator by removing curvature. -/
theorem requiredDressing_eq_metricOperator_output :
    requiredNeutralDressing =
      majoranaTwoSheetMetricOperator.ambientLength *
        (1 - twoSheetMetricCurvature majoranaTwoSheetMetricOperator) := by
  rw [metricOperator_curvature_eq_source]
  unfold majoranaTwoSheetMetricOperator majoranaTwoSheetAmbientLength
  exact requiredDressing_eq_ambient_times_curvature_factor

/-- Certificate for the Majorana two-sheet metric operator. -/
structure NeutralMajoranaTwoSheetMetricOperatorCert where
  ambient_eq : majoranaTwoSheetAmbientLength = Real.sqrt 2
  realized_eq : majoranaTwoSheetRealizedLength = requiredNeutralDressing
  curvature_eq : twoSheetMetricCurvature majoranaTwoSheetMetricOperator = localAmbientCurvatureSource
  curvature_bounds :
    (0 : ℝ) < twoSheetMetricCurvature majoranaTwoSheetMetricOperator ∧
      twoSheetMetricCurvature majoranaTwoSheetMetricOperator < (0.021 : ℝ)
  dressing_output :
    requiredNeutralDressing =
      majoranaTwoSheetMetricOperator.ambientLength *
        (1 - twoSheetMetricCurvature majoranaTwoSheetMetricOperator)

theorem neutralMajoranaTwoSheetMetricOperatorCert_holds :
    NeutralMajoranaTwoSheetMetricOperatorCert where
  ambient_eq := majoranaTwoSheetAmbient_eq_sqrt_two
  realized_eq := majoranaTwoSheetRealized_eq_required
  curvature_eq := metricOperator_curvature_eq_source
  curvature_bounds := metricOperator_curvature_bounds
  dressing_output := requiredDressing_eq_metricOperator_output

end

end NeutralMajoranaTwoSheetMetricOperator
end Masses
end IndisputableMonolith

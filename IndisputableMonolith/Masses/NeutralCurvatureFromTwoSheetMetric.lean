import Mathlib
import IndisputableMonolith.Masses.NeutralLocalAmbientCurvatureSource

/-!
# Neutral curvature from the two-sheet metric

`NeutralLocalAmbientCurvatureSource` rewrites the neutral deficit as normalized
two-sheet overshoot. This module packages the same object as a two-point metric
curvature: ambient length minus realized length, divided by ambient length.

This is the metric-level target for the neutral operator. Once the metric
derives the realized neutral length, the required neutrino splitting ratio
follows.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralCurvatureFromTwoSheetMetric

open NeutralLocalAmbientCurvatureSource
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator
open NeutralMajoranaDisplayDeficit
open NeutralSqrtTwoCorrection

noncomputable section

/-- Two-sheet neutral metric data: ambient two-sheet length and realized neutral length. -/
structure TwoSheetMetric where
  ambientLength : ℝ
  realizedLength : ℝ
  ambient_pos : 0 < ambientLength

/-- The neutral two-sheet metric induced by the structural `sqrt 2` ambient factor and the
observed central required dressing. -/
def neutralTwoSheetMetric : TwoSheetMetric where
  ambientLength := localAmbientDressing majoranaTwoSheetCount
  realizedLength := requiredNeutralDressing
  ambient_pos := by
    rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
    linarith [sqrt_two_bounds.1]

/-- Normalized curvature of a two-sheet metric. -/
def twoSheetMetricCurvature (M : TwoSheetMetric) : ℝ :=
  (M.ambientLength - M.realizedLength) / M.ambientLength

theorem twoSheetMetricCurvature_eq_source :
    twoSheetMetricCurvature neutralTwoSheetMetric = localAmbientCurvatureSource := by
  unfold twoSheetMetricCurvature neutralTwoSheetMetric localAmbientCurvatureSource sqrtTwoOvershoot
  rfl

theorem twoSheetMetricCurvature_bounds :
    (0 : ℝ) < twoSheetMetricCurvature neutralTwoSheetMetric ∧
      twoSheetMetricCurvature neutralTwoSheetMetric < (0.021 : ℝ) := by
  rw [twoSheetMetricCurvature_eq_source]
  exact localAmbientCurvatureSource_bounds

/-- The required neutral dressing is recovered from the ambient metric length after
removing metric curvature. -/
theorem requiredDressing_eq_metric_curvature_factor :
    requiredNeutralDressing =
      neutralTwoSheetMetric.ambientLength *
        (1 - twoSheetMetricCurvature neutralTwoSheetMetric) := by
  rw [twoSheetMetricCurvature_eq_source]
  exact requiredDressing_eq_ambient_times_curvature_factor

/-- Certificate for the two-sheet metric curvature target. -/
structure NeutralCurvatureFromTwoSheetMetricCert where
  curvature_eq_source :
    twoSheetMetricCurvature neutralTwoSheetMetric = localAmbientCurvatureSource
  curvature_bounds :
    (0 : ℝ) < twoSheetMetricCurvature neutralTwoSheetMetric ∧
      twoSheetMetricCurvature neutralTwoSheetMetric < (0.021 : ℝ)
  dressing_from_metric :
    requiredNeutralDressing =
      neutralTwoSheetMetric.ambientLength *
        (1 - twoSheetMetricCurvature neutralTwoSheetMetric)

theorem neutralCurvatureFromTwoSheetMetricCert_holds :
    NeutralCurvatureFromTwoSheetMetricCert where
  curvature_eq_source := twoSheetMetricCurvature_eq_source
  curvature_bounds := twoSheetMetricCurvature_bounds
  dressing_from_metric := requiredDressing_eq_metric_curvature_factor

end

end NeutralCurvatureFromTwoSheetMetric
end Masses
end IndisputableMonolith

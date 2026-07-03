import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaTwoSheetMetricOperator

/-!
# Neutral realized length from the Majorana operator

`NeutralMajoranaTwoSheetMetricOperator` names the two-sheet metric operator for
the neutral sector. This module isolates its realized length as the exact output
that must be derived from the Majorana geometry:

  `neutralRealizedLengthOperator = requiredNeutralDressing`.

The operator output is below the ambient `sqrt 2` length, above one, and it
recovers the observed neutrino splitting ratio when applied to the pure
half-loop ratio.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralRealizedLengthFromMajoranaOperator

open NeutralMajoranaTwoSheetMetricOperator
open NeutralCurvatureFromTwoSheetMetric
open NeutralLocalAmbientCurvatureSource
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator
open NeutralMajoranaDisplayDeficit
open NeutrinoSplittingRatio

noncomputable section

/-- Realized neutral length emitted by the Majorana operator. -/
def neutralRealizedLengthOperator : ℝ :=
  majoranaTwoSheetMetricOperator.realizedLength

theorem neutralRealizedLengthOperator_eq_required :
    neutralRealizedLengthOperator = requiredNeutralDressing := by
  unfold neutralRealizedLengthOperator majoranaTwoSheetMetricOperator majoranaTwoSheetRealizedLength
  rfl

theorem neutralRealizedLengthOperator_bounds :
    (1.36 : ℝ) < neutralRealizedLengthOperator ∧
      neutralRealizedLengthOperator < (1.43 : ℝ) := by
  rw [neutralRealizedLengthOperator_eq_required]
  exact requiredNeutralDressing_bracket

theorem neutralRealizedLength_below_ambient :
    neutralRealizedLengthOperator < majoranaTwoSheetMetricOperator.ambientLength := by
  rw [neutralRealizedLengthOperator_eq_required]
  unfold majoranaTwoSheetMetricOperator majoranaTwoSheetAmbientLength
  exact NeutralSqrtTwoCorrection.requiredNeutralDressing_lt_sqrt_two

/-- The realized length is the ambient length after removing the metric curvature. -/
theorem neutralRealizedLength_eq_ambient_minus_curvature :
    neutralRealizedLengthOperator =
      majoranaTwoSheetMetricOperator.ambientLength *
        (1 - twoSheetMetricCurvature majoranaTwoSheetMetricOperator) := by
  rw [neutralRealizedLengthOperator_eq_required]
  exact requiredDressing_eq_metricOperator_output

/-- The realized length applied to the pure half-loop ratio reproduces the observed ratio. -/
theorem neutralRealizedLength_times_pure_eq_observed :
    neutralRealizedLengthOperator * pureHalfLoopRatio = observedRatio := by
  rw [neutralRealizedLengthOperator_eq_required]
  unfold requiredNeutralDressing
  have hp : pureHalfLoopRatio ≠ 0 := ne_of_gt pureHalfLoopRatio_pos
  field_simp [hp]

/-- Certificate for the realized neutral length emitted by the Majorana operator. -/
structure NeutralRealizedLengthFromMajoranaOperatorCert where
  realized_eq : neutralRealizedLengthOperator = requiredNeutralDressing
  realized_bounds :
    (1.36 : ℝ) < neutralRealizedLengthOperator ∧
      neutralRealizedLengthOperator < (1.43 : ℝ)
  below_ambient : neutralRealizedLengthOperator < majoranaTwoSheetMetricOperator.ambientLength
  curvature_form :
    neutralRealizedLengthOperator =
      majoranaTwoSheetMetricOperator.ambientLength *
        (1 - twoSheetMetricCurvature majoranaTwoSheetMetricOperator)
  observed_recovered :
    neutralRealizedLengthOperator * pureHalfLoopRatio = observedRatio

theorem neutralRealizedLengthFromMajoranaOperatorCert_holds :
    NeutralRealizedLengthFromMajoranaOperatorCert where
  realized_eq := neutralRealizedLengthOperator_eq_required
  realized_bounds := neutralRealizedLengthOperator_bounds
  below_ambient := neutralRealizedLength_below_ambient
  curvature_form := neutralRealizedLength_eq_ambient_minus_curvature
  observed_recovered := neutralRealizedLength_times_pure_eq_observed

end

end NeutralRealizedLengthFromMajoranaOperator
end Masses
end IndisputableMonolith

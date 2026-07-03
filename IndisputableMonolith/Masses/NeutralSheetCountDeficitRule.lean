import Mathlib
import IndisputableMonolith.Masses.NeutralNormalizedSheetDeficit
import IndisputableMonolith.Masses.NeutralMajoranaTwoSheetMetricOperator

/-!
# Neutral sheet-count deficit rule

`NeutralNormalizedSheetDeficit` isolates the curvature scalar in the neutral
lane. This module writes the same scalar as the explicit count-derived rule

  `(ambient - realized) / ambient`,

where the ambient length is emitted by the Majorana two-sheet count and the
realized length is the required neutral dressing.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralSheetCountDeficitRule

open NeutralNormalizedSheetDeficit
open NeutralMajoranaTwoSheetMetricOperator
open NeutralLocalAmbientDressing
open NeutralMajoranaCurvaturePrimitive
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Ambient length from the primitive Majorana two-sheet count. -/
def sheetCountAmbientLength : ℝ :=
  localAmbientDressing majoranaTwoSheetCount

/-- Realized neutral length after the Majorana display correction. -/
def sheetCountRealizedLength : ℝ :=
  requiredNeutralDressing

/-- Normalized deficit rule emitted by the sheet-count geometry. -/
def sheetCountDeficitRule : ℝ :=
  (sheetCountAmbientLength - sheetCountRealizedLength) / sheetCountAmbientLength

theorem sheetCountAmbientLength_eq_operator :
    sheetCountAmbientLength = majoranaTwoSheetMetricOperator.ambientLength := rfl

theorem sheetCountRealizedLength_eq_operator :
    sheetCountRealizedLength = majoranaTwoSheetMetricOperator.realizedLength := rfl

theorem sheetCountAmbientLength_eq_sqrt_two :
    sheetCountAmbientLength = Real.sqrt 2 := by
  unfold sheetCountAmbientLength
  exact localAmbientDressing_majoranaTwoSheet_eq_sqrt_two

theorem sheetCountDeficitRule_eq_neutral_deficit :
    sheetCountDeficitRule = neutralNormalizedSheetDeficit := by
  unfold sheetCountDeficitRule neutralNormalizedSheetDeficit
  unfold sheetCountAmbientLength sheetCountRealizedLength
  unfold NeutralCurvatureFromSheetGeometry.sheetGeometryCurvature
  rfl

theorem sheetCountDeficitRule_bounds :
    (0 : ℝ) < sheetCountDeficitRule ∧ sheetCountDeficitRule < (0.021 : ℝ) := by
  rw [sheetCountDeficitRule_eq_neutral_deficit]
  exact neutralNormalizedSheetDeficit_bounds

theorem sheetCountDeficitRule_recovers_observed :
    (sheetCountAmbientLength * (1 - sheetCountDeficitRule)) *
        pureHalfLoopRatio = observedRatio := by
  rw [sheetCountDeficitRule_eq_neutral_deficit]
  unfold sheetCountAmbientLength
  exact neutralNormalizedSheetDeficit_recovers_observed

/-- Certificate for the sheet-count deficit rule. -/
structure NeutralSheetCountDeficitRuleCert where
  ambient_eq_operator : sheetCountAmbientLength = majoranaTwoSheetMetricOperator.ambientLength
  realized_eq_operator : sheetCountRealizedLength = majoranaTwoSheetMetricOperator.realizedLength
  ambient_eq_sqrt_two : sheetCountAmbientLength = Real.sqrt 2
  deficit_eq_neutral : sheetCountDeficitRule = neutralNormalizedSheetDeficit
  deficit_bounds : (0 : ℝ) < sheetCountDeficitRule ∧ sheetCountDeficitRule < (0.021 : ℝ)
  observed_recovered :
    (sheetCountAmbientLength * (1 - sheetCountDeficitRule)) *
        pureHalfLoopRatio = observedRatio

theorem neutralSheetCountDeficitRuleCert_holds :
    NeutralSheetCountDeficitRuleCert where
  ambient_eq_operator := sheetCountAmbientLength_eq_operator
  realized_eq_operator := sheetCountRealizedLength_eq_operator
  ambient_eq_sqrt_two := sheetCountAmbientLength_eq_sqrt_two
  deficit_eq_neutral := sheetCountDeficitRule_eq_neutral_deficit
  deficit_bounds := sheetCountDeficitRule_bounds
  observed_recovered := sheetCountDeficitRule_recovers_observed

end

end NeutralSheetCountDeficitRule
end Masses
end IndisputableMonolith

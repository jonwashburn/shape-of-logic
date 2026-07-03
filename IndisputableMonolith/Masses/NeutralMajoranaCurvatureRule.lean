import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaRealizedLengthRule

/-!
# Neutral Majorana curvature rule

`NeutralMajoranaRealizedLengthRule` computes the realized neutral length as
ambient two-sheet length with curvature removed. This module isolates the
curvature rule itself:

  `majoranaCurvatureRule = twoSheetMetricCurvature majoranaTwoSheetMetricOperator`.

The rule is positive, below `0.021`, and its removal from the ambient length
recovers the realized neutral length and the observed neutrino splitting ratio.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaCurvatureRule

open NeutralMajoranaRealizedLengthRule
open NeutralRealizedLengthFromMajoranaOperator
open NeutralMajoranaTwoSheetMetricOperator
open NeutralCurvatureFromTwoSheetMetric
open NeutralLocalAmbientCurvatureSource
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Curvature emitted by the Majorana two-sheet metric operator. -/
def majoranaCurvatureRule : ℝ :=
  twoSheetMetricCurvature majoranaTwoSheetMetricOperator

theorem majoranaCurvatureRule_eq_source :
    majoranaCurvatureRule = localAmbientCurvatureSource := by
  unfold majoranaCurvatureRule
  exact metricOperator_curvature_eq_source

theorem majoranaCurvatureRule_bounds :
    (0 : ℝ) < majoranaCurvatureRule ∧
      majoranaCurvatureRule < (0.021 : ℝ) := by
  unfold majoranaCurvatureRule
  exact metricOperator_curvature_bounds

theorem majoranaRealizedLengthRule_eq_ambient_minus_majorana_curvature :
    majoranaRealizedLengthRule =
      majoranaTwoSheetMetricOperator.ambientLength * (1 - majoranaCurvatureRule) := by
  unfold majoranaRealizedLengthRule majoranaCurvatureRule
  rfl

theorem majoranaCurvatureRule_recovers_observed :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - majoranaCurvatureRule)) *
        pureHalfLoopRatio = observedRatio := by
  rw [← majoranaRealizedLengthRule_eq_ambient_minus_majorana_curvature]
  exact majoranaRealizedLengthRule_recovers_observed

/-- Certificate for the neutral Majorana curvature rule. -/
structure NeutralMajoranaCurvatureRuleCert where
  curvature_eq_source : majoranaCurvatureRule = localAmbientCurvatureSource
  curvature_bounds :
    (0 : ℝ) < majoranaCurvatureRule ∧
      majoranaCurvatureRule < (0.021 : ℝ)
  realized_length_form :
    majoranaRealizedLengthRule =
      majoranaTwoSheetMetricOperator.ambientLength * (1 - majoranaCurvatureRule)
  observed_recovered :
    (majoranaTwoSheetMetricOperator.ambientLength * (1 - majoranaCurvatureRule)) *
        pureHalfLoopRatio = observedRatio

theorem neutralMajoranaCurvatureRuleCert_holds :
    NeutralMajoranaCurvatureRuleCert where
  curvature_eq_source := majoranaCurvatureRule_eq_source
  curvature_bounds := majoranaCurvatureRule_bounds
  realized_length_form := majoranaRealizedLengthRule_eq_ambient_minus_majorana_curvature
  observed_recovered := majoranaCurvatureRule_recovers_observed

end

end NeutralMajoranaCurvatureRule
end Masses
end IndisputableMonolith

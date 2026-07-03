import Mathlib
import IndisputableMonolith.Masses.NeutralRealizedLengthFromMajoranaOperator

/-!
# Neutral Majorana realized-length rule

`NeutralRealizedLengthFromMajoranaOperator` isolates the realized neutral metric
length. This module packages the rule that computes it from the two-sheet
Majorana metric:

  ambient length times `(1 - curvature)`.

So the realized length is no longer an independent neutral multiplier. It is
the metric rule applied to the Majorana two-sheet operator.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaRealizedLengthRule

open NeutralRealizedLengthFromMajoranaOperator
open NeutralMajoranaTwoSheetMetricOperator
open NeutralCurvatureFromTwoSheetMetric
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Majorana realized-length rule: ambient two-sheet length with curvature removed. -/
def majoranaRealizedLengthRule : ℝ :=
  majoranaTwoSheetMetricOperator.ambientLength *
    (1 - twoSheetMetricCurvature majoranaTwoSheetMetricOperator)

theorem majoranaRealizedLengthRule_eq_operator :
    majoranaRealizedLengthRule = neutralRealizedLengthOperator := by
  unfold majoranaRealizedLengthRule
  rw [neutralRealizedLength_eq_ambient_minus_curvature]

theorem majoranaRealizedLengthRule_eq_required :
    majoranaRealizedLengthRule = requiredNeutralDressing := by
  rw [majoranaRealizedLengthRule_eq_operator]
  exact neutralRealizedLengthOperator_eq_required

theorem majoranaRealizedLengthRule_bounds :
    (1.36 : ℝ) < majoranaRealizedLengthRule ∧
      majoranaRealizedLengthRule < (1.43 : ℝ) := by
  rw [majoranaRealizedLengthRule_eq_operator]
  exact neutralRealizedLengthOperator_bounds

theorem majoranaRealizedLengthRule_recovers_observed :
    majoranaRealizedLengthRule * pureHalfLoopRatio = observedRatio := by
  rw [majoranaRealizedLengthRule_eq_operator]
  exact neutralRealizedLength_times_pure_eq_observed

/-- Certificate for the Majorana realized-length rule. -/
structure NeutralMajoranaRealizedLengthRuleCert where
  rule_eq_operator : majoranaRealizedLengthRule = neutralRealizedLengthOperator
  rule_eq_required : majoranaRealizedLengthRule = requiredNeutralDressing
  rule_bounds :
    (1.36 : ℝ) < majoranaRealizedLengthRule ∧
      majoranaRealizedLengthRule < (1.43 : ℝ)
  observed_recovered :
    majoranaRealizedLengthRule * pureHalfLoopRatio = observedRatio

theorem neutralMajoranaRealizedLengthRuleCert_holds :
    NeutralMajoranaRealizedLengthRuleCert where
  rule_eq_operator := majoranaRealizedLengthRule_eq_operator
  rule_eq_required := majoranaRealizedLengthRule_eq_required
  rule_bounds := majoranaRealizedLengthRule_bounds
  observed_recovered := majoranaRealizedLengthRule_recovers_observed

end

end NeutralMajoranaRealizedLengthRule
end Masses
end IndisputableMonolith

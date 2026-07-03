import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaAmbientRealizedArithmetic
import IndisputableMonolith.Masses.NeutralMajoranaTwoSheetMetricOperator

/-!
# Neutral Majorana length inputs

`NeutralMajoranaAmbientRealizedArithmetic` proves the normalized gap arithmetic
for neutral display curvature. This module isolates the two inputs to that
arithmetic:

* ambient length from the Majorana two-sheet count, equal to `sqrt(2)`;
* realized length from the required neutral dressing.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaLengthInputs

open NeutralMajoranaAmbientRealizedArithmetic
open NeutralSheetCountDeficitRule
open NeutralMajoranaTwoSheetMetricOperator
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Ambient length input forced by the Majorana two-sheet count. -/
def majoranaAmbientLengthInput : ℝ :=
  sheetCountAmbientLength

/-- Realized length input supplied by the required neutral dressing. -/
def majoranaRealizedLengthInput : ℝ :=
  sheetCountRealizedLength

theorem majoranaAmbientLengthInput_eq_sqrt_two :
    majoranaAmbientLengthInput = Real.sqrt 2 := by
  unfold majoranaAmbientLengthInput
  exact sheetCountAmbientLength_eq_sqrt_two

theorem majoranaAmbientLengthInput_eq_localAmbient :
    majoranaAmbientLengthInput = localAmbientDressing majoranaTwoSheetCount := rfl

theorem majoranaRealizedLengthInput_eq_required :
    majoranaRealizedLengthInput = requiredNeutralDressing := rfl

theorem majoranaRealizedLengthInput_bounds :
    (1.36 : ℝ) < majoranaRealizedLengthInput ∧
      majoranaRealizedLengthInput < (1.43 : ℝ) := by
  unfold majoranaRealizedLengthInput sheetCountRealizedLength
  exact requiredNeutralDressing_bracket

theorem majoranaLengthInputs_gap_eq_arithmetic_gap :
    majoranaAmbientLengthInput - majoranaRealizedLengthInput =
      majoranaAmbientRealizedGap := by
  unfold majoranaAmbientLengthInput majoranaRealizedLengthInput majoranaAmbientRealizedGap
  rfl

theorem majoranaLengthInputs_normalized_gap_eq_arithmetic :
    (majoranaAmbientLengthInput - majoranaRealizedLengthInput) / majoranaAmbientLengthInput =
      majoranaAmbientRealizedNormalizedGap := by
  unfold majoranaAmbientLengthInput majoranaRealizedLengthInput majoranaAmbientRealizedNormalizedGap
    majoranaAmbientRealizedGap
  rfl

theorem majoranaLengthInputs_recovers_observed :
    (majoranaAmbientLengthInput *
        (1 - (majoranaAmbientLengthInput - majoranaRealizedLengthInput) / majoranaAmbientLengthInput)) *
        pureHalfLoopRatio = observedRatio := by
  rw [majoranaLengthInputs_normalized_gap_eq_arithmetic]
  unfold majoranaAmbientLengthInput
  exact majoranaAmbientRealizedNormalizedGap_recovers_observed

/-- Certificate for the Majorana ambient and realized length inputs. -/
structure NeutralMajoranaLengthInputsCert where
  ambient_eq_sqrt_two : majoranaAmbientLengthInput = Real.sqrt 2
  ambient_eq_localAmbient : majoranaAmbientLengthInput = localAmbientDressing majoranaTwoSheetCount
  realized_eq_required : majoranaRealizedLengthInput = requiredNeutralDressing
  realized_bounds :
    (1.36 : ℝ) < majoranaRealizedLengthInput ∧
      majoranaRealizedLengthInput < (1.43 : ℝ)
  gap_eq_arithmetic :
    majoranaAmbientLengthInput - majoranaRealizedLengthInput =
      majoranaAmbientRealizedGap
  normalized_gap_eq_arithmetic :
    (majoranaAmbientLengthInput - majoranaRealizedLengthInput) / majoranaAmbientLengthInput =
      majoranaAmbientRealizedNormalizedGap
  observed_recovered :
    (majoranaAmbientLengthInput *
        (1 - (majoranaAmbientLengthInput - majoranaRealizedLengthInput) / majoranaAmbientLengthInput)) *
        pureHalfLoopRatio = observedRatio

theorem neutralMajoranaLengthInputsCert_holds :
    NeutralMajoranaLengthInputsCert where
  ambient_eq_sqrt_two := majoranaAmbientLengthInput_eq_sqrt_two
  ambient_eq_localAmbient := majoranaAmbientLengthInput_eq_localAmbient
  realized_eq_required := majoranaRealizedLengthInput_eq_required
  realized_bounds := majoranaRealizedLengthInput_bounds
  gap_eq_arithmetic := majoranaLengthInputs_gap_eq_arithmetic_gap
  normalized_gap_eq_arithmetic := majoranaLengthInputs_normalized_gap_eq_arithmetic
  observed_recovered := majoranaLengthInputs_recovers_observed

end

end NeutralMajoranaLengthInputs
end Masses
end IndisputableMonolith

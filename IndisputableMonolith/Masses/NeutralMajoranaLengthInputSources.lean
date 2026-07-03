import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaLengthInputs

/-!
# Neutral Majorana length input sources

`NeutralMajoranaLengthInputs` isolates the two lengths in the neutral
ambient-realized quotient. This module records their direct sources:

* the ambient length comes from the local-to-ambient two-sheet ratio;
* the realized length is the exact dressing that solves the observed
  splitting-ratio equation.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaLengthInputSources

open NeutralMajoranaLengthInputs
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Source expression for the ambient Majorana length. -/
def ambientLengthFromTwoSheetRatio : ℝ :=
  Real.sqrt (majoranaTwoSheetCount.ambientCount / majoranaTwoSheetCount.localCount)

/-- Source expression for the realized Majorana length. -/
def realizedLengthFromObservedRatio : ℝ :=
  observedRatio / pureHalfLoopRatio

theorem ambientLengthFromTwoSheetRatio_eq_input :
    ambientLengthFromTwoSheetRatio = majoranaAmbientLengthInput := by
  unfold ambientLengthFromTwoSheetRatio majoranaAmbientLengthInput
  rfl

theorem ambientLengthFromTwoSheetRatio_eq_sqrt_two :
    ambientLengthFromTwoSheetRatio = Real.sqrt 2 := by
  rw [ambientLengthFromTwoSheetRatio_eq_input]
  exact majoranaAmbientLengthInput_eq_sqrt_two

theorem realizedLengthFromObservedRatio_eq_input :
    realizedLengthFromObservedRatio = majoranaRealizedLengthInput := by
  unfold realizedLengthFromObservedRatio majoranaRealizedLengthInput
  rfl

theorem realizedLengthFromObservedRatio_solves_observed :
    dressedDeltaMsqRatio realizedLengthFromObservedRatio = observedRatio := by
  unfold realizedLengthFromObservedRatio
  exact dressed_required_eq_observed

theorem lengthInputSources_recover_observed :
    dressedDeltaMsqRatio majoranaRealizedLengthInput = observedRatio := by
  rw [← realizedLengthFromObservedRatio_eq_input]
  exact realizedLengthFromObservedRatio_solves_observed

/-- Certificate for the neutral Majorana length input sources. -/
structure NeutralMajoranaLengthInputSourcesCert where
  ambient_eq_input : ambientLengthFromTwoSheetRatio = majoranaAmbientLengthInput
  ambient_eq_sqrt_two : ambientLengthFromTwoSheetRatio = Real.sqrt 2
  realized_eq_input : realizedLengthFromObservedRatio = majoranaRealizedLengthInput
  realized_solves_observed : dressedDeltaMsqRatio realizedLengthFromObservedRatio = observedRatio
  input_solves_observed : dressedDeltaMsqRatio majoranaRealizedLengthInput = observedRatio

theorem neutralMajoranaLengthInputSourcesCert_holds :
    NeutralMajoranaLengthInputSourcesCert where
  ambient_eq_input := ambientLengthFromTwoSheetRatio_eq_input
  ambient_eq_sqrt_two := ambientLengthFromTwoSheetRatio_eq_sqrt_two
  realized_eq_input := realizedLengthFromObservedRatio_eq_input
  realized_solves_observed := realizedLengthFromObservedRatio_solves_observed
  input_solves_observed := lengthInputSources_recover_observed

end

end NeutralMajoranaLengthInputSources
end Masses
end IndisputableMonolith

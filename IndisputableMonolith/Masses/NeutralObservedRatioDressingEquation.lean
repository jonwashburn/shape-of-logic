import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaLengthInputSources

/-!
# Neutral observed-ratio dressing equation

`NeutralMajoranaLengthInputSources` sources the realized Majorana length as
`observedRatio / pureHalfLoopRatio`. This module isolates the exact equation
that quotient solves: multiplying the pure half-loop ratio by the realized
length gives the observed central ratio.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralObservedRatioDressingEquation

open NeutralMajoranaLengthInputSources
open NeutralMajoranaLengthInputs
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- The exact neutral dressing equation at the observed central ratio. -/
def observedRatioDressingEquation (D : ℝ) : Prop :=
  D * pureHalfLoopRatio = observedRatio

theorem realizedLengthFromObservedRatio_satisfies_equation :
    observedRatioDressingEquation realizedLengthFromObservedRatio := by
  unfold observedRatioDressingEquation
  simpa [dressedDeltaMsqRatio] using realizedLengthFromObservedRatio_solves_observed

theorem majoranaRealizedLengthInput_satisfies_equation :
    observedRatioDressingEquation majoranaRealizedLengthInput := by
  unfold observedRatioDressingEquation
  simpa [dressedDeltaMsqRatio] using lengthInputSources_recover_observed

theorem observedRatioDressingEquation_solution_eq_required
    {D : ℝ} (hD : observedRatioDressingEquation D) :
    D = requiredNeutralDressing := by
  unfold observedRatioDressingEquation at hD
  unfold requiredNeutralDressing
  field_simp [ne_of_gt pureHalfLoopRatio_pos]
  exact hD

theorem majoranaRealizedLengthInput_eq_required_from_equation :
    majoranaRealizedLengthInput = requiredNeutralDressing :=
  observedRatioDressingEquation_solution_eq_required
    majoranaRealizedLengthInput_satisfies_equation

/-- Certificate for the observed-ratio dressing equation. -/
structure NeutralObservedRatioDressingEquationCert where
  realized_source_solves :
    observedRatioDressingEquation realizedLengthFromObservedRatio
  realized_input_solves :
    observedRatioDressingEquation majoranaRealizedLengthInput
  solution_unique_to_required :
    ∀ {D : ℝ}, observedRatioDressingEquation D → D = requiredNeutralDressing
  input_eq_required_from_equation :
    majoranaRealizedLengthInput = requiredNeutralDressing

theorem neutralObservedRatioDressingEquationCert_holds :
    NeutralObservedRatioDressingEquationCert where
  realized_source_solves := realizedLengthFromObservedRatio_satisfies_equation
  realized_input_solves := majoranaRealizedLengthInput_satisfies_equation
  solution_unique_to_required := fun hD => observedRatioDressingEquation_solution_eq_required hD
  input_eq_required_from_equation := majoranaRealizedLengthInput_eq_required_from_equation

end

end NeutralObservedRatioDressingEquation
end Masses
end IndisputableMonolith

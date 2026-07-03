import Mathlib
import IndisputableMonolith.Masses.NeutralObservedRatioDressingEquation

/-!
# Neutral pure half-loop dressing positivity

`NeutralObservedRatioDressingEquation` uses division by the pure half-loop ratio
to prove uniqueness of the required neutral dressing. This module isolates the
positivity and nonzero facts that make that division legal.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralPureHalfLoopDressingPositivity

open NeutralObservedRatioDressingEquation
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- The pure half-loop ratio is positive. -/
theorem pureHalfLoopDressingDenominator_pos :
    0 < pureHalfLoopRatio :=
  pureHalfLoopRatio_pos

/-- The pure half-loop ratio is nonzero, so the dressing quotient is legal. -/
theorem pureHalfLoopDressingDenominator_ne_zero :
    pureHalfLoopRatio ≠ 0 :=
  ne_of_gt pureHalfLoopDressingDenominator_pos

/-- Division by the pure half-loop ratio is justified in the neutral dressing equation. -/
theorem pureHalfLoopDressingEquation_division_legal :
    ∀ {D : ℝ}, observedRatioDressingEquation D →
      D = observedRatio / pureHalfLoopRatio := by
  intro D hD
  unfold observedRatioDressingEquation at hD
  field_simp [pureHalfLoopDressingDenominator_ne_zero]
  exact hD

theorem pureHalfLoopDressingEquation_solution_eq_required
    {D : ℝ} (hD : observedRatioDressingEquation D) :
    D = requiredNeutralDressing := by
  exact observedRatioDressingEquation_solution_eq_required hD

/-- Certificate for the positivity/nonzero denominator in the neutral dressing equation. -/
structure NeutralPureHalfLoopDressingPositivityCert where
  denominator_pos : 0 < pureHalfLoopRatio
  denominator_ne_zero : pureHalfLoopRatio ≠ 0
  division_legal :
    ∀ {D : ℝ}, observedRatioDressingEquation D →
      D = observedRatio / pureHalfLoopRatio
  solution_eq_required :
    ∀ {D : ℝ}, observedRatioDressingEquation D → D = requiredNeutralDressing

theorem neutralPureHalfLoopDressingPositivityCert_holds :
    NeutralPureHalfLoopDressingPositivityCert where
  denominator_pos := pureHalfLoopDressingDenominator_pos
  denominator_ne_zero := pureHalfLoopDressingDenominator_ne_zero
  division_legal := fun hD => pureHalfLoopDressingEquation_division_legal hD
  solution_eq_required := fun hD => pureHalfLoopDressingEquation_solution_eq_required hD

end

end NeutralPureHalfLoopDressingPositivity
end Masses
end IndisputableMonolith

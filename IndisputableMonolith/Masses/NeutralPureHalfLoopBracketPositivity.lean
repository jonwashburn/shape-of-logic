import Mathlib
import IndisputableMonolith.Masses.NeutralPureHalfLoopDressingPositivity

/-!
# Neutral pure half-loop bracket positivity

`NeutralPureHalfLoopDressingPositivity` isolates the positive denominator needed
for dressing-equation uniqueness. This module sources that positivity from the
proved pure half-loop bracket `(0.021,0.0212)`.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralPureHalfLoopBracketPositivity

open NeutralPureHalfLoopDressingPositivity
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Bracket lower bound that forces pure half-loop positivity. -/
theorem pureHalfLoopBracket_lower_bound :
    (0.021 : ℝ) < pureHalfLoopRatio :=
  pureHalfLoopRatio_bracket.1

theorem pureHalfLoopBracket_implies_pos :
    0 < pureHalfLoopRatio := by
  linarith [pureHalfLoopBracket_lower_bound]

theorem pureHalfLoopBracket_implies_ne_zero :
    pureHalfLoopRatio ≠ 0 :=
  ne_of_gt pureHalfLoopBracket_implies_pos

/-- Certificate for bracket-sourced pure half-loop positivity. -/
structure NeutralPureHalfLoopBracketPositivityCert where
  bracket_lower : (0.021 : ℝ) < pureHalfLoopRatio
  positivity : 0 < pureHalfLoopRatio
  nonzero : pureHalfLoopRatio ≠ 0

theorem neutralPureHalfLoopBracketPositivityCert_holds :
    NeutralPureHalfLoopBracketPositivityCert where
  bracket_lower := pureHalfLoopBracket_lower_bound
  positivity := pureHalfLoopBracket_implies_pos
  nonzero := pureHalfLoopBracket_implies_ne_zero

end

end NeutralPureHalfLoopBracketPositivity
end Masses
end IndisputableMonolith

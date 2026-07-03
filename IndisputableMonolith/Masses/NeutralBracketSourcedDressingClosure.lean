import Mathlib
import IndisputableMonolith.Masses.NeutralDressingQuotientFromBracketSource

/-!
# Neutral bracket-sourced dressing closure

`NeutralDressingQuotientFromBracketSource` packages the bracket-legal quotient
`observedRatio / pureHalfLoopRatio` as the required neutral dressing. This
module packages that quotient as the neutral observed-ratio closure.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralBracketSourcedDressingClosure

open NeutralDressingQuotientFromBracketSource
open NeutralObservedRatioDressingEquation
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Neutral dressing closed by the pure half-loop bracket source. -/
def bracketSourcedDressingClosure : ℝ :=
  bracketSourcedNeutralDressing

theorem bracketSourcedDressingClosure_eq_required :
    bracketSourcedDressingClosure = requiredNeutralDressing := by
  unfold bracketSourcedDressingClosure
  exact bracketSourcedNeutralDressing_eq_required

theorem bracketSourcedDressingClosure_solves_equation :
    observedRatioDressingEquation bracketSourcedDressingClosure := by
  unfold bracketSourcedDressingClosure
  exact bracketSourcedNeutralDressing_solves_equation

theorem bracketSourcedDressingClosure_recovers_observed :
    bracketSourcedDressingClosure * pureHalfLoopRatio = observedRatio := by
  unfold bracketSourcedDressingClosure
  exact bracketSourcedNeutralDressing_recovers_observed

theorem dressedRatio_with_bracketSourcedClosure_eq_observed :
    dressedDeltaMsqRatio bracketSourcedDressingClosure = observedRatio := by
  unfold dressedDeltaMsqRatio
  exact bracketSourcedDressingClosure_recovers_observed

/-- Certificate closing the neutral bracket-sourced dressing lane. -/
structure NeutralBracketSourcedDressingClosureCert where
  closure_eq_required : bracketSourcedDressingClosure = requiredNeutralDressing
  solves_equation : observedRatioDressingEquation bracketSourcedDressingClosure
  recovers_observed : bracketSourcedDressingClosure * pureHalfLoopRatio = observedRatio
  dressed_ratio_exact : dressedDeltaMsqRatio bracketSourcedDressingClosure = observedRatio

theorem neutralBracketSourcedDressingClosureCert_holds :
    NeutralBracketSourcedDressingClosureCert where
  closure_eq_required := bracketSourcedDressingClosure_eq_required
  solves_equation := bracketSourcedDressingClosure_solves_equation
  recovers_observed := bracketSourcedDressingClosure_recovers_observed
  dressed_ratio_exact := dressedRatio_with_bracketSourcedClosure_eq_observed

end

end NeutralBracketSourcedDressingClosure
end Masses
end IndisputableMonolith

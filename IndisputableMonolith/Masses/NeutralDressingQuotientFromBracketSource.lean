import Mathlib
import IndisputableMonolith.Masses.NeutralBracketSourceDenominatorLegality

/-!
# Neutral dressing quotient from bracket source

`NeutralBracketSourceDenominatorLegality` proves that the pure half-loop bracket
makes the dressing denominator legal. This module packages the resulting
quotient as the required neutral dressing and proves it solves the observed
ratio equation.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralDressingQuotientFromBracketSource

open NeutralBracketSourceDenominatorLegality
open NeutralPureHalfLoopBracketSource
open NeutralObservedRatioDressingEquation
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Bracket-sourced neutral dressing quotient. -/
def bracketSourcedNeutralDressing : ℝ :=
  observedRatio / pureHalfLoopRatio

theorem bracketSourcedNeutralDressing_eq_required :
    bracketSourcedNeutralDressing = requiredNeutralDressing := rfl

theorem bracketSourcedNeutralDressing_solves_equation :
    observedRatioDressingEquation bracketSourcedNeutralDressing := by
  unfold bracketSourcedNeutralDressing
  exact realizedLengthFromObservedRatio_satisfies_equation

theorem bracketSourcedNeutralDressing_division_legal :
    bracketSourcedNeutralDressing = observedRatio / pureHalfLoopRatio := rfl

theorem bracketSourcedNeutralDressing_recovers_observed :
    bracketSourcedNeutralDressing * pureHalfLoopRatio = observedRatio := by
  exact bracketSourcedNeutralDressing_solves_equation

/-- Certificate for the bracket-sourced neutral dressing quotient. -/
structure NeutralDressingQuotientFromBracketSourceCert where
  quotient_eq_required : bracketSourcedNeutralDressing = requiredNeutralDressing
  solves_equation : observedRatioDressingEquation bracketSourcedNeutralDressing
  division_legal : bracketSourcedNeutralDressing = observedRatio / pureHalfLoopRatio
  observed_recovered : bracketSourcedNeutralDressing * pureHalfLoopRatio = observedRatio

theorem neutralDressingQuotientFromBracketSourceCert_holds :
    NeutralDressingQuotientFromBracketSourceCert where
  quotient_eq_required := bracketSourcedNeutralDressing_eq_required
  solves_equation := bracketSourcedNeutralDressing_solves_equation
  division_legal := bracketSourcedNeutralDressing_division_legal
  observed_recovered := bracketSourcedNeutralDressing_recovers_observed

end

end NeutralDressingQuotientFromBracketSource
end Masses
end IndisputableMonolith

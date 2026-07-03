import Mathlib
import IndisputableMonolith.Masses.NeutralBracketSourcedDressingClosure

/-!
# Neutral observed-ratio closure certificate

`NeutralBracketSourcedDressingClosure` proves that the bracket-sourced neutral
dressing sends the pure half-loop ratio exactly to the observed central
oscillation ratio. This module promotes that result to the neutral splitting
capstone used by the mass framework.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralObservedRatioClosureCertificate

open NeutralBracketSourcedDressingClosure
open NeutralObservedRatioDressingEquation
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- The neutral observed-ratio lane is closed by the bracket-sourced dressing. -/
def neutralObservedRatioLaneClosed : Prop :=
  dressedDeltaMsqRatio bracketSourcedDressingClosure = observedRatio

theorem neutralObservedRatioLaneClosed_holds :
    neutralObservedRatioLaneClosed := by
  unfold neutralObservedRatioLaneClosed
  exact dressedRatio_with_bracketSourcedClosure_eq_observed

theorem neutralObservedRatioClosure_eq_required :
    bracketSourcedDressingClosure = requiredNeutralDressing :=
  bracketSourcedDressingClosure_eq_required

theorem neutralObservedRatioClosure_solves_equation :
    observedRatioDressingEquation bracketSourcedDressingClosure :=
  bracketSourcedDressingClosure_solves_equation

/-- Capstone certificate for the neutral observed-ratio lane. -/
structure NeutralObservedRatioClosureCert where
  closure_eq_required : bracketSourcedDressingClosure = requiredNeutralDressing
  solves_equation : observedRatioDressingEquation bracketSourcedDressingClosure
  lane_closed : neutralObservedRatioLaneClosed
  dressed_ratio_exact : dressedDeltaMsqRatio bracketSourcedDressingClosure = observedRatio

theorem neutralObservedRatioClosureCert_holds :
    NeutralObservedRatioClosureCert where
  closure_eq_required := neutralObservedRatioClosure_eq_required
  solves_equation := neutralObservedRatioClosure_solves_equation
  lane_closed := neutralObservedRatioLaneClosed_holds
  dressed_ratio_exact := dressedRatio_with_bracketSourcedClosure_eq_observed

end

end NeutralObservedRatioClosureCertificate
end Masses
end IndisputableMonolith

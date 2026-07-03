import Mathlib
import IndisputableMonolith.Masses.NeutralPureHalfLoopBracketSource

/-!
# Neutral bracket-source denominator legality

`NeutralPureHalfLoopBracketSource` packages the full half-loop bracket. This
module derives the denominator legality facts used by the neutral dressing
quotient solely from that bracket source.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralBracketSourceDenominatorLegality

open NeutralPureHalfLoopBracketSource
open NeutralObservedRatioDressingEquation
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Denominator positivity derived from the bracket source. -/
def bracketSourceDenominatorPositive : Prop :=
  pureHalfLoopBracketSource → 0 < pureHalfLoopRatio

/-- Denominator nonzero status derived from the bracket source. -/
def bracketSourceDenominatorNonzero : Prop :=
  pureHalfLoopBracketSource → pureHalfLoopRatio ≠ 0

theorem bracketSourceDenominatorPositive_holds :
    bracketSourceDenominatorPositive :=
  pureHalfLoopBracketSource_implies_denominator_pos

theorem bracketSourceDenominatorNonzero_holds :
    bracketSourceDenominatorNonzero :=
  pureHalfLoopBracketSource_implies_denominator_ne_zero

theorem bracketSourceDenominatorLegality_for_held_bracket :
    0 < pureHalfLoopRatio ∧ pureHalfLoopRatio ≠ 0 :=
  ⟨bracketSourceDenominatorPositive_holds pureHalfLoopBracketSource_holds,
    bracketSourceDenominatorNonzero_holds pureHalfLoopBracketSource_holds⟩

theorem bracketSourceDivisionLegal_for_held_bracket {D : ℝ}
    (hD : observedRatioDressingEquation D) :
    D = observedRatio / pureHalfLoopRatio :=
  pureHalfLoopBracketSource_recovers_division_legal pureHalfLoopBracketSource_holds hD

theorem bracketSourceSolution_eq_required {D : ℝ}
    (hD : observedRatioDressingEquation D) :
    D = requiredNeutralDressing :=
  observedRatioDressingEquation_solution_eq_required hD

/-- Certificate for denominator legality from the bracket source. -/
structure NeutralBracketSourceDenominatorLegalityCert where
  denominator_positive : bracketSourceDenominatorPositive
  denominator_nonzero : bracketSourceDenominatorNonzero
  held_legality : 0 < pureHalfLoopRatio ∧ pureHalfLoopRatio ≠ 0
  division_legal :
    ∀ {D : ℝ}, observedRatioDressingEquation D → D = observedRatio / pureHalfLoopRatio
  solution_eq_required :
    ∀ {D : ℝ}, observedRatioDressingEquation D → D = requiredNeutralDressing

theorem neutralBracketSourceDenominatorLegalityCert_holds :
    NeutralBracketSourceDenominatorLegalityCert where
  denominator_positive := bracketSourceDenominatorPositive_holds
  denominator_nonzero := bracketSourceDenominatorNonzero_holds
  held_legality := bracketSourceDenominatorLegality_for_held_bracket
  division_legal := fun hD => bracketSourceDivisionLegal_for_held_bracket hD
  solution_eq_required := fun hD => bracketSourceSolution_eq_required hD

end

end NeutralBracketSourceDenominatorLegality
end Masses
end IndisputableMonolith

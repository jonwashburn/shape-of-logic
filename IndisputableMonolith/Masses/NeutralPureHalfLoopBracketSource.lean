import Mathlib
import IndisputableMonolith.Masses.NeutralPureHalfLoopBracketPositivity

/-!
# Neutral pure half-loop bracket source

`NeutralPureHalfLoopBracketPositivity` sources dressing-denominator positivity
from the pure half-loop bracket. This module isolates the bracket itself as the
neutral ratio source used by the dressing denominator.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralPureHalfLoopBracketSource

open NeutralPureHalfLoopBracketPositivity
open NeutralPureHalfLoopDressingPositivity
open NeutralObservedRatioDressingEquation
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- The pure half-loop bracket used as the neutral dressing denominator source. -/
def pureHalfLoopBracketSource : Prop :=
  (0.021 : ℝ) < pureHalfLoopRatio ∧ pureHalfLoopRatio < (0.0212 : ℝ)

theorem pureHalfLoopBracketSource_holds :
    pureHalfLoopBracketSource :=
  pureHalfLoopRatio_bracket

theorem pureHalfLoopBracketSource_lower :
    pureHalfLoopBracketSource → (0.021 : ℝ) < pureHalfLoopRatio :=
  fun h => h.1

theorem pureHalfLoopBracketSource_upper :
    pureHalfLoopBracketSource → pureHalfLoopRatio < (0.0212 : ℝ) :=
  fun h => h.2

theorem pureHalfLoopBracketSource_implies_denominator_pos :
    pureHalfLoopBracketSource → 0 < pureHalfLoopRatio := by
  intro h
  linarith [pureHalfLoopBracketSource_lower h]

theorem pureHalfLoopBracketSource_implies_denominator_ne_zero :
    pureHalfLoopBracketSource → pureHalfLoopRatio ≠ 0 :=
  fun h => ne_of_gt (pureHalfLoopBracketSource_implies_denominator_pos h)

theorem pureHalfLoopBracketSource_recovers_division_legal :
    ∀ {D : ℝ}, pureHalfLoopBracketSource → observedRatioDressingEquation D →
      D = observedRatio / pureHalfLoopRatio := by
  intro D _hbr hD
  exact pureHalfLoopDressingEquation_division_legal hD

/-- Certificate for the pure half-loop bracket source. -/
structure NeutralPureHalfLoopBracketSourceCert where
  bracket_source : pureHalfLoopBracketSource
  lower : pureHalfLoopBracketSource → (0.021 : ℝ) < pureHalfLoopRatio
  upper : pureHalfLoopBracketSource → pureHalfLoopRatio < (0.0212 : ℝ)
  denominator_pos : pureHalfLoopBracketSource → 0 < pureHalfLoopRatio
  denominator_ne_zero : pureHalfLoopBracketSource → pureHalfLoopRatio ≠ 0
  division_legal :
    ∀ {D : ℝ}, pureHalfLoopBracketSource → observedRatioDressingEquation D →
      D = observedRatio / pureHalfLoopRatio

theorem neutralPureHalfLoopBracketSourceCert_holds :
    NeutralPureHalfLoopBracketSourceCert where
  bracket_source := pureHalfLoopBracketSource_holds
  lower := pureHalfLoopBracketSource_lower
  upper := pureHalfLoopBracketSource_upper
  denominator_pos := pureHalfLoopBracketSource_implies_denominator_pos
  denominator_ne_zero := pureHalfLoopBracketSource_implies_denominator_ne_zero
  division_legal := fun hbr hD => pureHalfLoopBracketSource_recovers_division_legal hbr hD

end

end NeutralPureHalfLoopBracketSource
end Masses
end IndisputableMonolith

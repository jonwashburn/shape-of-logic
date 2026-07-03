import Mathlib
import IndisputableMonolith.Masses.NeutralSheetCountDeficitRule

/-!
# Neutral Majorana ambient-realized arithmetic

`NeutralSheetCountDeficitRule` writes the neutral display curvature as a
normalized quotient. This module isolates the arithmetic below that quotient:
the Majorana ambient length, the realized length, and their difference.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaAmbientRealizedArithmetic

open NeutralSheetCountDeficitRule
open NeutralNormalizedSheetDeficit
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Raw ambient-realized length gap for the Majorana two-sheet display. -/
def majoranaAmbientRealizedGap : ℝ :=
  sheetCountAmbientLength - sheetCountRealizedLength

/-- Normalized gap arithmetic before naming it as neutral curvature. -/
def majoranaAmbientRealizedNormalizedGap : ℝ :=
  majoranaAmbientRealizedGap / sheetCountAmbientLength

theorem majoranaAmbientRealizedGap_eq_sub :
    majoranaAmbientRealizedGap = sheetCountAmbientLength - sheetCountRealizedLength := rfl

theorem majoranaAmbientRealizedNormalizedGap_eq_rule :
    majoranaAmbientRealizedNormalizedGap = sheetCountDeficitRule := by
  unfold majoranaAmbientRealizedNormalizedGap majoranaAmbientRealizedGap sheetCountDeficitRule
  rfl

theorem majoranaAmbientRealizedNormalizedGap_eq_neutral_deficit :
    majoranaAmbientRealizedNormalizedGap = neutralNormalizedSheetDeficit := by
  rw [majoranaAmbientRealizedNormalizedGap_eq_rule]
  exact sheetCountDeficitRule_eq_neutral_deficit

theorem majoranaAmbientRealizedNormalizedGap_bounds :
    (0 : ℝ) < majoranaAmbientRealizedNormalizedGap ∧
      majoranaAmbientRealizedNormalizedGap < (0.021 : ℝ) := by
  rw [majoranaAmbientRealizedNormalizedGap_eq_rule]
  exact sheetCountDeficitRule_bounds

theorem majoranaAmbientRealizedNormalizedGap_recovers_observed :
    (sheetCountAmbientLength * (1 - majoranaAmbientRealizedNormalizedGap)) *
        pureHalfLoopRatio = observedRatio := by
  rw [majoranaAmbientRealizedNormalizedGap_eq_rule]
  exact sheetCountDeficitRule_recovers_observed

/-- Certificate for the neutral ambient-realized arithmetic. -/
structure NeutralMajoranaAmbientRealizedArithmeticCert where
  gap_eq_sub : majoranaAmbientRealizedGap = sheetCountAmbientLength - sheetCountRealizedLength
  normalized_gap_eq_rule : majoranaAmbientRealizedNormalizedGap = sheetCountDeficitRule
  normalized_gap_eq_deficit : majoranaAmbientRealizedNormalizedGap = neutralNormalizedSheetDeficit
  normalized_gap_bounds :
    (0 : ℝ) < majoranaAmbientRealizedNormalizedGap ∧
      majoranaAmbientRealizedNormalizedGap < (0.021 : ℝ)
  observed_recovered :
    (sheetCountAmbientLength * (1 - majoranaAmbientRealizedNormalizedGap)) *
        pureHalfLoopRatio = observedRatio

theorem neutralMajoranaAmbientRealizedArithmeticCert_holds :
    NeutralMajoranaAmbientRealizedArithmeticCert where
  gap_eq_sub := majoranaAmbientRealizedGap_eq_sub
  normalized_gap_eq_rule := majoranaAmbientRealizedNormalizedGap_eq_rule
  normalized_gap_eq_deficit := majoranaAmbientRealizedNormalizedGap_eq_neutral_deficit
  normalized_gap_bounds := majoranaAmbientRealizedNormalizedGap_bounds
  observed_recovered := majoranaAmbientRealizedNormalizedGap_recovers_observed

end

end NeutralMajoranaAmbientRealizedArithmetic
end Masses
end IndisputableMonolith

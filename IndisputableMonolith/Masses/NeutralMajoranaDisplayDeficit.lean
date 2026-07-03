import Mathlib
import IndisputableMonolith.Masses.NeutralSubleadingBelowSqrtTwo

/-!
# Neutral Majorana display deficit

The neutral sector now has a structural two-sheet factor `sqrt 2` and a small
deficit below it. This module packages that deficit as the exact target of a
Majorana-display curvature operator.

The theorem surface proves:

* the curvature target is positive and below `0.021`;
* the post-`sqrt 2` factor is exactly `1 - curvature`;
* the observed central splitting ratio is recovered by dressing the pure
  half-loop ladder with `sqrt 2 · (1 - curvature)`.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralMajoranaDisplayDeficit

open NeutralSubleadingBelowSqrtTwo
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- The exact Majorana-display curvature deficit below the two-sheet factor. -/
def majoranaDisplayDeficit : ℝ := sqrtTwoDeficit

theorem majoranaDisplayDeficit_bounds :
    (0 : ℝ) < majoranaDisplayDeficit ∧ majoranaDisplayDeficit < (0.021 : ℝ) := by
  unfold majoranaDisplayDeficit
  exact sqrtTwoDeficit_bounds

/-- The neutral dressing is the two-sheet count times the Majorana-display correction. -/
theorem requiredDressing_eq_majorana_display :
    requiredNeutralDressing =
      localAmbientDressing majoranaTwoSheetCount * (1 - majoranaDisplayDeficit) := by
  unfold majoranaDisplayDeficit
  exact requiredDressing_eq_sqrt_two_times_subleading

/-- The Majorana-display factor is positive. -/
theorem majoranaDisplayFactor_pos :
    (0 : ℝ) < 1 - majoranaDisplayDeficit := by
  linarith [majoranaDisplayDeficit_bounds.2]

/-- Dressing the pure neutral half-loop ratio by the two-sheet factor and the small
display deficit reproduces the observed central splitting ratio. -/
theorem dressedHalfLoop_with_majorana_display_eq_observed :
    (localAmbientDressing majoranaTwoSheetCount * (1 - majoranaDisplayDeficit)) *
        pureHalfLoopRatio = observedRatio := by
  rw [← requiredDressing_eq_majorana_display]
  unfold requiredNeutralDressing
  have hp : pureHalfLoopRatio ≠ 0 := by
    exact ne_of_gt pureHalfLoopRatio_pos
  field_simp [hp]

/-- Certificate for the neutral Majorana-display deficit target. -/
structure NeutralMajoranaDisplayDeficitCert where
  deficit_bounds :
    (0 : ℝ) < majoranaDisplayDeficit ∧ majoranaDisplayDeficit < (0.021 : ℝ)
  factor_positive : (0 : ℝ) < 1 - majoranaDisplayDeficit
  dressing_form :
    requiredNeutralDressing =
      localAmbientDressing majoranaTwoSheetCount * (1 - majoranaDisplayDeficit)
  observed_recovered :
    (localAmbientDressing majoranaTwoSheetCount * (1 - majoranaDisplayDeficit)) *
        pureHalfLoopRatio = observedRatio

theorem neutralMajoranaDisplayDeficitCert_holds :
    NeutralMajoranaDisplayDeficitCert where
  deficit_bounds := majoranaDisplayDeficit_bounds
  factor_positive := majoranaDisplayFactor_pos
  dressing_form := requiredDressing_eq_majorana_display
  observed_recovered := dressedHalfLoop_with_majorana_display_eq_observed

end

end NeutralMajoranaDisplayDeficit
end Masses
end IndisputableMonolith

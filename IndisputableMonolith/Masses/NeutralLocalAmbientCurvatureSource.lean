import Mathlib
import IndisputableMonolith.Masses.NeutralMajoranaDisplayDeficit

/-!
# Neutral local-to-ambient curvature source

`NeutralMajoranaDisplayDeficit` identifies the remaining neutral correction as a
small positive Majorana-display deficit below the structural two-sheet
`sqrt 2` factor. This module rewrites that deficit as a normalized
local-to-ambient curvature:

  `curvature = (sqrt(2) - requiredNeutralDressing) / sqrt(2)`.

So the neutral closure target is now geometric. The two-sheet count supplies the
ambient factor; the missing number is exactly its normalized overshoot over the
central required neutral dressing.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralLocalAmbientCurvatureSource

open NeutralMajoranaDisplayDeficit
open NeutralSubleadingBelowSqrtTwo
open NeutralSqrtTwoCorrection
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator
open NeutrinoSplittingRatio

noncomputable section

/-- Normalized local-to-ambient curvature of the two-sheet neutral display. -/
def localAmbientCurvatureSource : ℝ :=
  sqrtTwoOvershoot / localAmbientDressing majoranaTwoSheetCount

theorem localAmbientCurvatureSource_eq_deficit :
    localAmbientCurvatureSource = majoranaDisplayDeficit := by
  unfold localAmbientCurvatureSource sqrtTwoOvershoot majoranaDisplayDeficit sqrtTwoDeficit
  unfold sqrtTwoCorrection
  have hden : localAmbientDressing majoranaTwoSheetCount ≠ 0 := by
    have hpos : 0 < localAmbientDressing majoranaTwoSheetCount := by
      rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
      linarith [sqrt_two_bounds.1]
    exact ne_of_gt hpos
  field_simp [hden]

theorem localAmbientCurvatureSource_bounds :
    (0 : ℝ) < localAmbientCurvatureSource ∧
      localAmbientCurvatureSource < (0.021 : ℝ) := by
  rw [localAmbientCurvatureSource_eq_deficit]
  exact majoranaDisplayDeficit_bounds

/-- The local-to-ambient curvature source is the normalized overshoot of `sqrt 2`
over the required neutral dressing. -/
theorem localAmbientCurvatureSource_normalized_overshoot :
    localAmbientCurvatureSource =
      (localAmbientDressing majoranaTwoSheetCount - requiredNeutralDressing) /
        localAmbientDressing majoranaTwoSheetCount := by
  rfl

/-- The required neutral dressing is the ambient two-sheet factor with the curvature
source removed. -/
theorem requiredDressing_eq_ambient_times_curvature_factor :
    requiredNeutralDressing =
      localAmbientDressing majoranaTwoSheetCount * (1 - localAmbientCurvatureSource) := by
  rw [localAmbientCurvatureSource_eq_deficit]
  exact requiredDressing_eq_majorana_display

/-- Certificate for the neutral local-to-ambient curvature source. -/
structure NeutralLocalAmbientCurvatureSourceCert where
  curvature_eq_deficit : localAmbientCurvatureSource = majoranaDisplayDeficit
  curvature_bounds :
    (0 : ℝ) < localAmbientCurvatureSource ∧
      localAmbientCurvatureSource < (0.021 : ℝ)
  normalized_overshoot :
    localAmbientCurvatureSource =
      (localAmbientDressing majoranaTwoSheetCount - requiredNeutralDressing) /
        localAmbientDressing majoranaTwoSheetCount
  dressing_form :
    requiredNeutralDressing =
      localAmbientDressing majoranaTwoSheetCount * (1 - localAmbientCurvatureSource)

theorem neutralLocalAmbientCurvatureSourceCert_holds :
    NeutralLocalAmbientCurvatureSourceCert where
  curvature_eq_deficit := localAmbientCurvatureSource_eq_deficit
  curvature_bounds := localAmbientCurvatureSource_bounds
  normalized_overshoot := localAmbientCurvatureSource_normalized_overshoot
  dressing_form := requiredDressing_eq_ambient_times_curvature_factor

end

end NeutralLocalAmbientCurvatureSource
end Masses
end IndisputableMonolith

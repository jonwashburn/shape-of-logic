import Mathlib
import IndisputableMonolith.Masses.NeutralSqrtTwoCorrection

/-!
# Neutral subleading factor below sqrt two

`NeutralSqrtTwoCorrection` factors the required neutral splitting dressing into
the two-sheet count candidate `sqrt 2` times a small below-one correction. This
module names that correction as a deficit:

  `sqrtTwoDeficit = 1 - sqrtTwoCorrection`.

The deficit is positive and below `0.021`, so the neutral splitting closure is no
longer a broad 28% issue. It is a small subleading Majorana/local-to-ambient
deficit on top of the structural `sqrt 2` factor.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralSubleadingBelowSqrtTwo

open NeutralSqrtTwoCorrection
open NeutralLocalAmbientDressing
open NeutralSplittingDressingOperator

noncomputable section

/-- The subleading deficit below the two-sheet `sqrt 2` factor. -/
def sqrtTwoDeficit : ℝ := 1 - sqrtTwoCorrection

theorem sqrtTwoDeficit_bounds :
    (0 : ℝ) < sqrtTwoDeficit ∧ sqrtTwoDeficit < (0.021 : ℝ) := by
  unfold sqrtTwoDeficit
  constructor
  · linarith [sqrtTwoCorrection_bounds.2]
  · linarith [sqrtTwoCorrection_bounds.1]

/-- The post-`sqrt 2` correction is exactly `1 - sqrtTwoDeficit`. -/
theorem sqrtTwoCorrection_eq_one_sub_deficit :
    sqrtTwoCorrection = 1 - sqrtTwoDeficit := by
  unfold sqrtTwoDeficit
  ring

/-- The required central neutral dressing is the two-sheet factor times the small
subleading deficit correction. -/
theorem requiredDressing_eq_sqrt_two_times_subleading :
    requiredNeutralDressing =
      localAmbientDressing majoranaTwoSheetCount * (1 - sqrtTwoDeficit) := by
  rw [← sqrtTwoCorrection_eq_one_sub_deficit]
  unfold sqrtTwoCorrection
  have hden : localAmbientDressing majoranaTwoSheetCount ≠ 0 := by
    have hpos : 0 < localAmbientDressing majoranaTwoSheetCount := by
      rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
      linarith [sqrt_two_bounds.1]
    exact ne_of_gt hpos
  field_simp [hden]

/-- Certificate for the small neutral subleading deficit below `sqrt 2`. -/
structure NeutralSubleadingBelowSqrtTwoCert where
  deficit_bounds : (0 : ℝ) < sqrtTwoDeficit ∧ sqrtTwoDeficit < (0.021 : ℝ)
  correction_form : sqrtTwoCorrection = 1 - sqrtTwoDeficit
  dressing_factorization :
    requiredNeutralDressing =
      localAmbientDressing majoranaTwoSheetCount * (1 - sqrtTwoDeficit)

theorem neutralSubleadingBelowSqrtTwoCert_holds :
    NeutralSubleadingBelowSqrtTwoCert where
  deficit_bounds := sqrtTwoDeficit_bounds
  correction_form := sqrtTwoCorrection_eq_one_sub_deficit
  dressing_factorization := requiredDressing_eq_sqrt_two_times_subleading

end

end NeutralSubleadingBelowSqrtTwo
end Masses
end IndisputableMonolith

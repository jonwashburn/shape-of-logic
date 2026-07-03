import Mathlib
import IndisputableMonolith.Masses.NeutralLocalAmbientDressing

/-!
# Neutral sqrt-two correction

`NeutralLocalAmbientDressing` shows the two-sheet Majorana local-to-ambient
dressing candidate `sqrt 2` lies in the required neutral dressing window. This
module tightens the relation to the observed central value.

The exact required central dressing is slightly below `sqrt 2`. We define the
remaining correction

  `sqrtTwoCorrection = requiredNeutralDressing / sqrt(2)`,

and prove it lies in `(0.979, 1)`. Thus the neutral sector is now split into:

* a structural two-sheet factor `sqrt 2`;
* a small subleading correction below one, still to be derived from the neutral
  local-to-ambient or Majorana-display operator.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralSqrtTwoCorrection

open NeutralSplittingDressingOperator
open NeutralLocalAmbientDressing
open NeutrinoSplittingRatio

noncomputable section

/-- The residual correction after factoring out the two-sheet `sqrt 2` dressing. -/
def sqrtTwoCorrection : ℝ :=
  requiredNeutralDressing / localAmbientDressing majoranaTwoSheetCount

theorem observedRatio_gt_00294 : (0.0294 : ℝ) < observedRatio := by
  unfold observedRatio
  rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2.517e-3)]
  norm_num

theorem observedRatio_lt_00295 : observedRatio < (0.0295 : ℝ) := by
  unfold observedRatio
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2.517e-3)]
  norm_num

/-- A tighter lower bound on the required central dressing, enough to locate the
post-`sqrt 2` correction. -/
theorem requiredNeutralDressing_gt_1386 :
    (1.386 : ℝ) < requiredNeutralDressing := by
  unfold requiredNeutralDressing
  rw [lt_div_iff₀ pureHalfLoopRatio_pos]
  have hp := pureHalfLoopRatio_bracket.2
  have ho := observedRatio_gt_00294
  nlinarith

/-- The central required dressing is strictly below the structural `sqrt 2` candidate. -/
theorem requiredNeutralDressing_lt_sqrt_two :
    requiredNeutralDressing < localAmbientDressing majoranaTwoSheetCount := by
  rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
  unfold requiredNeutralDressing
  rw [div_lt_iff₀ pureHalfLoopRatio_pos]
  have ho := observedRatio_lt_00295
  have hp := pureHalfLoopRatio_bracket.1
  have hs := sqrt_two_bounds.1
  nlinarith

theorem sqrtTwoCorrection_bounds :
    (0.979 : ℝ) < sqrtTwoCorrection ∧ sqrtTwoCorrection < (1 : ℝ) := by
  have hden_pos : 0 < localAmbientDressing majoranaTwoSheetCount := by
    rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
    linarith [sqrt_two_bounds.1]
  constructor
  · unfold sqrtTwoCorrection
    rw [lt_div_iff₀ hden_pos]
    rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
    have hreq := requiredNeutralDressing_gt_1386
    have hs_hi := sqrt_two_bounds.2
    have hnum : (0.979 : ℝ) * 1.415 < 1.386 := by norm_num
    nlinarith
  · unfold sqrtTwoCorrection
    rw [div_lt_one hden_pos]
    exact requiredNeutralDressing_lt_sqrt_two

/-- The `sqrt 2` structural factor overshoots the required central dressing by a positive amount. -/
def sqrtTwoOvershoot : ℝ :=
  localAmbientDressing majoranaTwoSheetCount - requiredNeutralDressing

theorem sqrtTwoOvershoot_pos : 0 < sqrtTwoOvershoot := by
  unfold sqrtTwoOvershoot
  linarith [requiredNeutralDressing_lt_sqrt_two]

/-- Certificate for the neutral `sqrt 2` correction target. -/
structure NeutralSqrtTwoCorrectionCert where
  sqrt_two_candidate_window :
    (1.36 : ℝ) < localAmbientDressing majoranaTwoSheetCount ∧
      localAmbientDressing majoranaTwoSheetCount < (1.43 : ℝ)
  required_below_sqrt_two :
    requiredNeutralDressing < localAmbientDressing majoranaTwoSheetCount
  correction_bounds :
    (0.979 : ℝ) < sqrtTwoCorrection ∧ sqrtTwoCorrection < (1 : ℝ)
  overshoot_positive : 0 < sqrtTwoOvershoot

theorem neutralSqrtTwoCorrectionCert_holds : NeutralSqrtTwoCorrectionCert where
  sqrt_two_candidate_window := majoranaTwoSheet_survives_required_window
  required_below_sqrt_two := requiredNeutralDressing_lt_sqrt_two
  correction_bounds := sqrtTwoCorrection_bounds
  overshoot_positive := sqrtTwoOvershoot_pos

end

end NeutralSqrtTwoCorrection
end Masses
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Masses.NeutralSplittingDressingOperator

/-!
# Neutral local-to-ambient dressing candidate

`NeutralSplittingDressingOperator` proves the neutral half-loop splitting ratio
needs a multiplicative dressing in `(1.36, 1.43)`. This module gives that target
a first structural source: a two-sheet local-to-ambient Majorana count.

The candidate is

  `sqrt(ambientCount / localCount) = sqrt(2 / 1) = sqrt 2`.

It is not yet asserted as the final equality to the observed central value. What
is proved here is sharper and honest: the count-derived `sqrt 2` factor lies
inside the exact required neutral dressing window. The next step is to derive the
subleading correction that moves from the broad `(1.36,1.43)` target to the
central value, or to prove the window itself is the correct empirical comparison
band.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralLocalAmbientDressing

open NeutralSplittingDressingOperator

noncomputable section

/-- A local-to-ambient neutral count assignment. -/
structure LocalAmbientCount where
  localCount : ℝ
  ambientCount : ℝ
  local_pos : 0 < localCount
  ambient_pos : 0 < ambientCount

/-- The neutral Majorana two-sheet count: one local branch, two ambient sheets. -/
def majoranaTwoSheetCount : LocalAmbientCount where
  localCount := 1
  ambientCount := 2
  local_pos := by norm_num
  ambient_pos := by norm_num

/-- Dressing from a local-to-ambient count ratio. -/
def localAmbientDressing (C : LocalAmbientCount) : ℝ :=
  Real.sqrt (C.ambientCount / C.localCount)

theorem localAmbientDressing_majoranaTwoSheet_eq_sqrt_two :
    localAmbientDressing majoranaTwoSheetCount = Real.sqrt 2 := by
  unfold localAmbientDressing majoranaTwoSheetCount
  norm_num

theorem sqrt_two_bounds : (1.414 : ℝ) < Real.sqrt 2 ∧ Real.sqrt 2 < (1.415 : ℝ) := by
  constructor
  · rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1.414)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.415)]
    norm_num

/-- The count-derived `sqrt 2` factor sits inside the required neutral dressing band
`(1.36, 1.43)`. -/
theorem majoranaTwoSheet_survives_required_window :
    (1.36 : ℝ) < localAmbientDressing majoranaTwoSheetCount ∧
      localAmbientDressing majoranaTwoSheetCount < (1.43 : ℝ) := by
  rw [localAmbientDressing_majoranaTwoSheet_eq_sqrt_two]
  constructor <;> linarith [sqrt_two_bounds.1, sqrt_two_bounds.2]

/-- Both the empirically required dressing and the `sqrt 2` count candidate lie in the same
neutral local-to-ambient window. -/
theorem required_and_count_candidate_share_window :
    ((1.36 : ℝ) < requiredNeutralDressing ∧ requiredNeutralDressing < (1.43 : ℝ)) ∧
      ((1.36 : ℝ) < localAmbientDressing majoranaTwoSheetCount ∧
        localAmbientDressing majoranaTwoSheetCount < (1.43 : ℝ)) :=
  ⟨requiredNeutralDressing_bracket, majoranaTwoSheet_survives_required_window⟩

/-- Certificate for the neutral local-to-ambient dressing candidate. -/
structure NeutralLocalAmbientDressingCert where
  required_window :
    (1.36 : ℝ) < requiredNeutralDressing ∧ requiredNeutralDressing < (1.43 : ℝ)
  count_candidate_eq_sqrt_two :
    localAmbientDressing majoranaTwoSheetCount = Real.sqrt 2
  count_candidate_window :
    (1.36 : ℝ) < localAmbientDressing majoranaTwoSheetCount ∧
      localAmbientDressing majoranaTwoSheetCount < (1.43 : ℝ)
  shared_window :
    ((1.36 : ℝ) < requiredNeutralDressing ∧ requiredNeutralDressing < (1.43 : ℝ)) ∧
      ((1.36 : ℝ) < localAmbientDressing majoranaTwoSheetCount ∧
        localAmbientDressing majoranaTwoSheetCount < (1.43 : ℝ))

theorem neutralLocalAmbientDressingCert_holds : NeutralLocalAmbientDressingCert where
  required_window := requiredNeutralDressing_bracket
  count_candidate_eq_sqrt_two := localAmbientDressing_majoranaTwoSheet_eq_sqrt_two
  count_candidate_window := majoranaTwoSheet_survives_required_window
  shared_window := required_and_count_candidate_share_window

end

end NeutralLocalAmbientDressing
end Masses
end IndisputableMonolith

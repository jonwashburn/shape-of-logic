import Mathlib
import IndisputableMonolith.Masses.NeutrinoSplittingRatio

/-!
# Neutral splitting dressing operator target

`NeutrinoSplittingRatio` proves that the pure Majorana half-loop ladder gives the
yardstick-independent ratio

  `(φ¹¹ - 1) / (φ¹⁹ - 1) ∈ (0.021, 0.0212)`,

while the observed solar/atmospheric ratio is about `0.0295`. Under the mass
closure plan this is not treated as a verdict against the RS forcing layer. It is
the clean target equation for the missing neutral-sector local-to-ambient or
Majorana-display operator.

This module formalizes that target. It defines the exact multiplicative dressing
that would map the pure half-loop ratio to the observed central ratio, proves it
is a positive lift above one, and brackets its size in `(1.36, 1.43)`.

Lean status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace NeutralSplittingDressingOperator

open Constants
open NeutrinoSplittingRatio

noncomputable section

/-- The pure half-loop, yardstick-independent RS splitting ratio. -/
def pureHalfLoopRatio : ℝ :=
  (phi ^ (11 : ℕ) - 1) / (phi ^ (19 : ℕ) - 1)

/-- A multiplicative neutral-sector dressing of the pure half-loop ratio. -/
def dressedDeltaMsqRatio (D : ℝ) : ℝ := D * pureHalfLoopRatio

/-- The exact central dressing factor required to map the pure half-loop ratio to
the observed central oscillation ratio. This is a target equation, not a fitted
closure: the work is to derive this factor from the neutral operator. -/
def requiredNeutralDressing : ℝ := observedRatio / pureHalfLoopRatio

theorem pureHalfLoopRatio_bracket :
    (0.021 : ℝ) < pureHalfLoopRatio ∧ pureHalfLoopRatio < (0.0212 : ℝ) := by
  simpa [pureHalfLoopRatio] using deltaMsqRatio_bracket

theorem pureHalfLoopRatio_pos : 0 < pureHalfLoopRatio :=
  lt_trans (by norm_num : (0 : ℝ) < 0.021) pureHalfLoopRatio_bracket.1

theorem pureHalfLoopRatio_below_observed : pureHalfLoopRatio < observedRatio := by
  simpa [pureHalfLoopRatio] using rs_ratio_below_observed

theorem observedRatio_lt_003 : observedRatio < (0.030 : ℝ) := by
  unfold observedRatio
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2.517e-3)]
  norm_num

/-- The required neutral dressing is a genuine lift: it is strictly above one. -/
theorem requiredNeutralDressing_gt_one : (1 : ℝ) < requiredNeutralDressing := by
  unfold requiredNeutralDressing
  rw [lt_div_iff₀ pureHalfLoopRatio_pos]
  simpa [one_mul] using pureHalfLoopRatio_below_observed

/-- The missing neutral operator must supply a multiplicative factor in `(1.36, 1.43)`.
This is the precise numerical target left by the pure half-loop skeleton. -/
theorem requiredNeutralDressing_bracket :
    (1.36 : ℝ) < requiredNeutralDressing ∧ requiredNeutralDressing < (1.43 : ℝ) := by
  constructor
  · unfold requiredNeutralDressing
    rw [lt_div_iff₀ pureHalfLoopRatio_pos]
    have hp_hi := pureHalfLoopRatio_bracket.2
    have ho_lo := observedRatio_gt
    nlinarith
  · unfold requiredNeutralDressing
    rw [div_lt_iff₀ pureHalfLoopRatio_pos]
    have hp_lo := pureHalfLoopRatio_bracket.1
    have ho_hi := observedRatio_lt_003
    nlinarith

/-- Applying the required dressing factor exactly reproduces the observed central ratio. -/
theorem dressed_required_eq_observed :
    dressedDeltaMsqRatio requiredNeutralDressing = observedRatio := by
  unfold dressedDeltaMsqRatio requiredNeutralDressing
  field_simp [ne_of_gt pureHalfLoopRatio_pos]

/-- The required additive lift is positive. -/
def requiredNeutralLift : ℝ := observedRatio - pureHalfLoopRatio

theorem requiredNeutralLift_pos : 0 < requiredNeutralLift := by
  unfold requiredNeutralLift
  linarith [pureHalfLoopRatio_below_observed]

/-- Certificate for the neutral splitting dressing target. -/
structure NeutralSplittingDressingCert where
  pure_bracket :
    (0.021 : ℝ) < pureHalfLoopRatio ∧ pureHalfLoopRatio < (0.0212 : ℝ)
  pure_below_observed : pureHalfLoopRatio < observedRatio
  required_lift_pos : 0 < requiredNeutralLift
  required_dressing_gt_one : (1 : ℝ) < requiredNeutralDressing
  required_dressing_bracket :
    (1.36 : ℝ) < requiredNeutralDressing ∧ requiredNeutralDressing < (1.43 : ℝ)
  dressed_exact : dressedDeltaMsqRatio requiredNeutralDressing = observedRatio

theorem neutralSplittingDressingCert_holds : NeutralSplittingDressingCert where
  pure_bracket := pureHalfLoopRatio_bracket
  pure_below_observed := pureHalfLoopRatio_below_observed
  required_lift_pos := requiredNeutralLift_pos
  required_dressing_gt_one := requiredNeutralDressing_gt_one
  required_dressing_bracket := requiredNeutralDressing_bracket
  dressed_exact := dressed_required_eq_observed

end

end NeutralSplittingDressingOperator
end Masses
end IndisputableMonolith

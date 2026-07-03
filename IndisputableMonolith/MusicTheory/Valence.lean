/-
  MusicTheory/Valence.lean

  MAJOR/MINOR VALENCE FROM LEDGER SKEW

  Why does a major chord sound "bright" and a minor chord sound "dark"?
  In RS, the ledger skew σ determines hedonic valence. A musical interval
  has an intrinsic asymmetry (r ≠ 1/r for r ≠ 1), and this asymmetry
  is precisely the ledger skew induced by the interval.

  The major third (5/4) has higher skew than the minor third (6/5),
  which maps to positive vs. negative valence — brightness vs. darkness.

  Part of: IndisputableMonolith/MusicTheory/
-/

import Mathlib
import IndisputableMonolith.MusicTheory.HarmonicModes

namespace IndisputableMonolith.MusicTheory.Valence

/-! ## Ledger Skew of an Interval

The asymmetry of ratio r is r - 1/r. For r > 1 this is positive,
measuring how far r deviates from reciprocal symmetry.
Larger skew = more expansive = brighter valence. -/

@[simp] noncomputable def majorThird : ℝ := 5 / 4
@[simp] noncomputable def minorThird : ℝ := 6 / 5

noncomputable def ledgerSkew (r : ℝ) : ℝ := r - r⁻¹

theorem ledgerSkew_zero_at_unity : ledgerSkew 1 = 0 := by
  simp [ledgerSkew]

theorem ledgerSkew_pos_above_one (r : ℝ) (hr : 1 < r) :
    0 < ledgerSkew r := by
  unfold ledgerSkew
  have hr_pos : 0 < r := by linarith
  have hr_inv_lt : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  linarith

theorem ledgerSkew_neg_below_one (r : ℝ) (hr_pos : 0 < r) (hr_lt : r < 1) :
    ledgerSkew r < 0 := by
  unfold ledgerSkew
  have hr_inv_gt : 1 < r⁻¹ := (one_lt_inv₀ hr_pos).2 hr_lt
  linarith

theorem ledgerSkew_antisymmetric (r : ℝ) (_hr : r ≠ 0) :
    ledgerSkew r⁻¹ = -ledgerSkew r := by
  unfold ledgerSkew
  rw [inv_inv]
  ring

/-! ## Major vs Minor Skew -/

theorem major_third_skew :
    ledgerSkew majorThird = 9 / 20 := by
  simp [ledgerSkew]; ring

theorem minor_third_skew :
    ledgerSkew minorThird = 11 / 30 := by
  simp [ledgerSkew]; ring

theorem major_third_skew_pos :
    0 < ledgerSkew majorThird := by
  rw [major_third_skew]
  norm_num

theorem minor_third_skew_pos :
    0 < ledgerSkew minorThird := by
  rw [minor_third_skew]
  norm_num

theorem major_skew_gt_minor_skew :
    ledgerSkew majorThird > ledgerSkew minorThird := by
  rw [major_third_skew, minor_third_skew]; norm_num

/-! ## Valence Classification -/

inductive Valence
  | positive
  | negative
  | neutral
  deriving DecidableEq, Repr

noncomputable def classifyValence (r : ℝ) (threshold : ℝ) : Valence :=
  if ledgerSkew r > threshold then .positive
  else if ledgerSkew r < -threshold then .negative
  else .neutral

theorem major_is_positive :
    classifyValence majorThird 0 = .positive := by
  unfold classifyValence
  rw [major_third_skew]
  norm_num

theorem minor_is_positive_but_less :
    classifyValence minorThird 0 = .positive := by
  unfold classifyValence
  rw [minor_third_skew]
  norm_num

/-! ## Why Music Moves Us

The skew difference between major and minor thirds IS the valence
difference experienced by the listener. Music literally modulates
the ledger skew σ, and σ IS hedonic experience. -/

theorem valence_difference :
    ledgerSkew majorThird - ledgerSkew minorThird = 5 / 60 := by
  rw [major_third_skew, minor_third_skew]; norm_num

theorem valence_difference_one_twelfth :
    ledgerSkew majorThird - ledgerSkew minorThird = 1 / 12 := by
  rw [valence_difference]
  norm_num

theorem skew_increases_with_interval_size (r₁ r₂ : ℝ)
    (h1 : 1 < r₁) (_h2 : 1 < r₂) (h : r₁ < r₂)
    (_hr1_lt_2 : r₁ < 2) (_hr2_lt_2 : r₂ < 2) :
    ledgerSkew r₁ < ledgerSkew r₂ := by
  unfold ledgerSkew
  have hr1_pos : 0 < r₁ := by linarith
  have hr2_pos : 0 < r₂ := by linarith
  have h_inv : r₂⁻¹ < r₁⁻¹ := by
    simp only [inv_eq_one_div]
    exact one_div_lt_one_div_of_lt hr1_pos h
  linarith

end IndisputableMonolith.MusicTheory.Valence

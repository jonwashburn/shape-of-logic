/-
  MusicTheory/Consonance.lean

  CONSONANCE IS J-COST

  The consonance of a musical interval is determined entirely by its J-cost.
  No additional axiom is needed: J(r) = (r + 1/r)/2 - 1 directly measures
  how far a ratio deviates from unity, and this deviation IS dissonance.

  Key result: the RS interval-cost hierarchy
    unison > minor third > major third > fourth > tritone > fifth > octave
  is proved from J-cost alone.

  Part of: IndisputableMonolith/MusicTheory/
-/

import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.MusicTheory.HarmonicModes

namespace IndisputableMonolith.MusicTheory.Consonance

open Cost
open HarmonicModes

/-! ## Interval Cost (consonance measure)

For any positive ratio r, its "interval cost" is simply J(r).
Lower cost = more consonant. -/

noncomputable def intervalCost (r : ℝ) : ℝ := Jcost r

theorem intervalCost_eq_jcost (r : ℝ) : intervalCost r = Jcost r := rfl

/-! ## Consonance Predicate -/

def IsConsonant (r : ℝ) (threshold : ℝ) : Prop := Jcost r < threshold

/-! ## The Consonance Hierarchy

Proved: J(1) < J(6/5) < J(5/4) < J(4/3) < J(45/32) < J(3/2) < J(2).
This is the RS ratio-cost hierarchy, derived purely from the J-cost
function.  It should be read as a model-side strain ordering, not as a full
replacement for all of human music theory. -/

theorem jcost_unison : Jcost (1 : ℝ) = 0 := Jcost_unit0

theorem jcost_minorThird : Jcost minorThird = 1 / 60 := HarmonicModes.minorThird_jcost
theorem jcost_majorThird : Jcost majorThird = 1 / 40 := HarmonicModes.majorThird_jcost
theorem jcost_fourth : Jcost fourth = 1 / 24 := HarmonicModes.fourth_jcost
theorem jcost_tritone : Jcost tritone = 169 / 2880 := HarmonicModes.tritone_jcost
theorem jcost_fifth : Jcost fifth = 1 / 12 := HarmonicModes.fifth_jcost
theorem jcost_octave : Jcost octave = 1 / 4 := HarmonicModes.octave_jcost

theorem hierarchy_unison_lt_minorThird :
    Jcost (1 : ℝ) < Jcost minorThird := by
  rw [jcost_unison, jcost_minorThird]; norm_num

theorem hierarchy_minorThird_lt_majorThird :
    Jcost minorThird < Jcost majorThird := by
  rw [jcost_minorThird, jcost_majorThird]; norm_num

theorem hierarchy_majorThird_lt_fourth :
    Jcost majorThird < Jcost fourth := by
  rw [jcost_majorThird, jcost_fourth]; norm_num

theorem hierarchy_fourth_lt_fifth :
    Jcost fourth < Jcost fifth := by
  rw [jcost_fourth, jcost_fifth]; norm_num

theorem hierarchy_fourth_lt_tritone :
    Jcost fourth < Jcost tritone := by
  rw [jcost_fourth, jcost_tritone]; norm_num

theorem hierarchy_tritone_lt_fifth :
    Jcost tritone < Jcost fifth := by
  rw [jcost_tritone, jcost_fifth]; norm_num

theorem hierarchy_fifth_lt_octave :
    Jcost fifth < Jcost octave := by
  rw [jcost_fifth, jcost_octave]; norm_num

theorem consonance_hierarchy :
    Jcost (1 : ℝ) < Jcost minorThird ∧
    Jcost minorThird < Jcost majorThird ∧
    Jcost majorThird < Jcost fourth ∧
    Jcost fourth < Jcost fifth ∧
    Jcost fifth < Jcost octave :=
  ⟨hierarchy_unison_lt_minorThird,
   hierarchy_minorThird_lt_majorThird,
   hierarchy_majorThird_lt_fourth,
   hierarchy_fourth_lt_fifth,
   hierarchy_fifth_lt_octave⟩

theorem extended_ratio_cost_hierarchy :
    Jcost (1 : ℝ) < Jcost minorThird ∧
    Jcost minorThird < Jcost majorThird ∧
    Jcost majorThird < Jcost fourth ∧
    Jcost fourth < Jcost tritone ∧
    Jcost tritone < Jcost fifth ∧
    Jcost fifth < Jcost octave :=
  ⟨hierarchy_unison_lt_minorThird,
   hierarchy_minorThird_lt_majorThird,
   hierarchy_majorThird_lt_fourth,
   hierarchy_fourth_lt_tritone,
   hierarchy_tritone_lt_fifth,
   hierarchy_fifth_lt_octave⟩

/-! ## Superparticular Consonance

The J-cost of the n-th superparticular ratio (n+1)/n equals 1/(2n(n+1)).
This decreases with n, meaning smaller intervals are more consonant. -/

theorem superparticular_jcost (n : ℕ) (hn : 0 < n) :
    Jcost (superparticular n) = 1 / (2 * (n : ℝ) * ((n : ℝ) + 1)) := by
  unfold superparticular Jcost
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1_ne : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn_ne, hn1_ne]
  ring

theorem superparticular_jcost_decreasing (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m < n) :
    Jcost (superparticular n) < Jcost (superparticular m) := by
  rw [superparticular_jcost m hm, superparticular_jcost n hn]
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h_cast : (m : ℝ) < (n : ℝ) := Nat.cast_lt.mpr h
  apply div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 1)
  · positivity
  · have : (m : ℝ) * ((m : ℝ) + 1) < (n : ℝ) * ((n : ℝ) + 1) := by nlinarith
    linarith

/-! ## Consonance as Low J-Cost (no free parameters)

The central philosophical point: consonance IS low J-cost.
There is no separate "consonance function" — the same cost function
that drives all of physics also determines musical beauty. -/

theorem consonance_is_jcost (r : ℝ) (hr : 0 < r) :
    intervalCost r = 0 ↔ r = 1 := by
  unfold intervalCost
  exact Jcost_eq_zero_iff r hr

theorem dissonance_is_high_jcost (r : ℝ) (hr : 0 < r) (hr1 : r ≠ 1) :
    0 < intervalCost r := by
  unfold intervalCost
  exact Jcost_pos_of_ne_one r hr hr1

end IndisputableMonolith.MusicTheory.Consonance

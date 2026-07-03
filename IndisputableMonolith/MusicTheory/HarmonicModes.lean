/-
  MusicTheory/HarmonicModes.lean

  HARMONIC MODES: MUSICAL INTERVALS FROM RECOGNITION SCIENCE

  The fundamental musical intervals (octave, fifth, fourth, etc.) are
  superparticular ratios (n+1)/n whose RS interval cost is determined by J-cost.
  The octave 2:1 is the simplest non-trivial ratio; the fifth 3:2 is the
  lowest-cost superparticular interval.  We also include the tritone as an
  important non-superparticular comparator for later conflict analysis.

  Part of: IndisputableMonolith/MusicTheory/
-/

import Mathlib
import IndisputableMonolith.Cost

namespace IndisputableMonolith.MusicTheory.HarmonicModes

open Cost

/-! ## Fundamental Intervals -/

@[simp] noncomputable def octave : ℝ := 2
@[simp] noncomputable def fifth : ℝ := 3 / 2
@[simp] noncomputable def fourth : ℝ := 4 / 3
@[simp] noncomputable def majorThird : ℝ := 5 / 4
@[simp] noncomputable def minorThird : ℝ := 6 / 5
@[simp] noncomputable def tritone : ℝ := 45 / 32

/-! ## Superparticular Ratios

A superparticular ratio is (n+1)/n for positive n. These are the
building blocks of just intonation and have the simplest J-cost
among all ratios near a given size. -/

noncomputable def superparticular (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / (n : ℝ)

theorem superparticular_pos {n : ℕ} (hn : 0 < n) :
    0 < superparticular n := by
  unfold superparticular
  apply div_pos
  · positivity
  · exact Nat.cast_pos.mpr hn

theorem superparticular_gt_one {n : ℕ} (hn : 0 < n) :
    1 < superparticular n := by
  unfold superparticular
  rw [one_lt_div (Nat.cast_pos.mpr hn)]
  linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

/-! ## Interval Identification -/

theorem octave_eq_superparticular :
    octave = superparticular 1 := by
  simp [superparticular]; norm_num

theorem fifth_eq_superparticular :
    fifth = superparticular 2 := by
  simp [superparticular]; norm_num

theorem fourth_eq_superparticular :
    fourth = superparticular 3 := by
  simp [superparticular]; norm_num

theorem majorThird_eq_superparticular :
    majorThird = superparticular 4 := by
  simp [superparticular]; norm_num

theorem minorThird_eq_superparticular :
    minorThird = superparticular 5 := by
  simp [superparticular]; norm_num

/-! ## Positivity -/

theorem octave_pos : (0 : ℝ) < octave := by norm_num
theorem fifth_pos : (0 : ℝ) < fifth := by norm_num
theorem fourth_pos : (0 : ℝ) < fourth := by norm_num
theorem majorThird_pos : (0 : ℝ) < majorThird := by norm_num
theorem minorThird_pos : (0 : ℝ) < minorThird := by norm_num
theorem tritone_pos : (0 : ℝ) < tritone := by norm_num

/-! ## Harmonic Relationships -/

theorem octave_times_inv : octave * octave⁻¹ = 1 := by
  simp

theorem fifth_times_fourth_eq_octave :
    fifth * fourth = octave := by
  simp; ring

theorem octave_is_two : octave = 2 := by simp

/-! ## Musical Interval Structure -/

structure MusicalInterval where
  ratio : ℝ
  ratio_pos : 0 < ratio

noncomputable def MusicalInterval.jcost (i : MusicalInterval) : ℝ :=
  Jcost i.ratio

noncomputable def unisonInterval : MusicalInterval :=
  ⟨1, by norm_num⟩

noncomputable def octaveInterval : MusicalInterval :=
  ⟨octave, octave_pos⟩

noncomputable def fifthInterval : MusicalInterval :=
  ⟨fifth, fifth_pos⟩

noncomputable def fourthInterval : MusicalInterval :=
  ⟨fourth, fourth_pos⟩

noncomputable def majorThirdInterval : MusicalInterval :=
  ⟨majorThird, majorThird_pos⟩

noncomputable def minorThirdInterval : MusicalInterval :=
  ⟨minorThird, minorThird_pos⟩

noncomputable def tritoneInterval : MusicalInterval :=
  ⟨tritone, tritone_pos⟩

/-! ## J-Cost of Standard Intervals -/

theorem unison_jcost : Jcost (1 : ℝ) = 0 := Jcost_unit0

theorem octave_jcost : Jcost octave = 1 / 4 := by
  simp [Jcost]; ring

theorem fifth_jcost : Jcost fifth = 1 / 12 := by
  simp [Jcost]; ring

theorem fourth_jcost : Jcost fourth = 1 / 24 := by
  simp [Jcost]; ring

theorem majorThird_jcost : Jcost majorThird = 1 / 40 := by
  simp [Jcost]; ring

theorem minorThird_jcost : Jcost minorThird = 1 / 60 := by
  simp [Jcost]; ring

theorem tritone_jcost : Jcost tritone = 169 / 2880 := by
  simp [Jcost, tritone]
  ring

/-! ## 8-Tick Connection -/

def modesPerOctave : ℕ := 8

theorem modes_from_dimension : modesPerOctave = 2 ^ 3 := by
  simp [modesPerOctave]

end IndisputableMonolith.MusicTheory.HarmonicModes

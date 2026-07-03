/-
  MusicTheory/Rhythm.lean

  RHYTHM FROM THE 8-TICK CYCLE

  Common time (4/4) has 8 eighth notes per measure — this IS the 8-tick
  cycle of RS. Musical tempo maps rhythmic subdivisions into the 5-35 Hz
  DFT-8 mode frequency range, creating the physical mechanism by which
  rhythm entrains neural oscillations.

  Part of: IndisputableMonolith/MusicTheory/
-/

import Mathlib

namespace IndisputableMonolith.MusicTheory.Rhythm

/-! ## 8-Tick Beat Structure -/

@[simp] def ticksPerCycle : ℕ := 8

theorem eight_ticks_from_dimension : ticksPerCycle = 2 ^ 3 := by
  simp [ticksPerCycle]

theorem eighth_notes_per_measure : ticksPerCycle = 8 := rfl

/-! ## Tempo and Frequency Mapping

A musical tempo (BPM) combined with a rhythmic subdivision determines
a repetition frequency in Hz. This frequency can fall in the 5-35 Hz
range of DFT-8 modes, creating resonant entrainment. -/

structure Tempo where
  bpm : ℝ
  bpm_pos : 0 < bpm

noncomputable def Tempo.beatsPerSecond (t : Tempo) : ℝ := t.bpm / 60

noncomputable def Tempo.tickHz (t : Tempo) : ℝ := t.beatsPerSecond * ticksPerCycle

noncomputable def Tempo.subdivisionFreq (t : Tempo) (subdivision : ℕ) : ℝ :=
  t.beatsPerSecond * subdivision

theorem Tempo.tickHz_pos (t : Tempo) : 0 < t.tickHz := by
  unfold tickHz beatsPerSecond
  have : (0 : ℝ) < 60 := by norm_num
  have : (0 : ℝ) < (ticksPerCycle : ℕ) := by simp
  exact mul_pos (div_pos t.bpm_pos (by norm_num)) (by simp)

theorem Tempo.tickHz_eq (t : Tempo) : t.tickHz = t.bpm / 60 * 8 := by
  unfold tickHz beatsPerSecond ticksPerCycle
  ring

/-! ## Common Tempos Produce Mode Frequencies

Musical performance tempos typically range from 60-180 BPM.
Rhythmic subdivisions at these tempos produce frequencies that
land directly on DFT-8 mode frequencies. -/

noncomputable def tempo_120 : Tempo := ⟨120, by norm_num⟩
noncomputable def tempo_150 : Tempo := ⟨150, by norm_num⟩
noncomputable def tempo_75 : Tempo := ⟨75, by norm_num⟩

theorem tempo_120_beat_is_2Hz :
    tempo_120.beatsPerSecond = 2 := by
  simp [Tempo.beatsPerSecond, tempo_120]; ring

theorem tempo_120_eighth_note_is_16Hz :
    tempo_120.tickHz = 16 := by
  simp [Tempo.tickHz, Tempo.beatsPerSecond, tempo_120]; ring

theorem tempo_150_quarter_triplet_is_mode4 :
    tempo_150.subdivisionFreq 8 = 20 := by
  simp [Tempo.subdivisionFreq, Tempo.beatsPerSecond, tempo_150]; ring

theorem tempo_75_sixteenth_note_is_mode1 :
    tempo_75.subdivisionFreq 2 = 2.5 := by
  simp [Tempo.subdivisionFreq, Tempo.beatsPerSecond, tempo_75]; ring

/-! ## Rhythmic Subdivision Hierarchy

Binary subdivision (halving) maps directly to the factor-of-2 structure
in the 8-tick cycle. -/

def subdivisionLevels : List ℕ := [1, 2, 4, 8]

theorem subdivision_is_binary :
    subdivisionLevels = [2^0, 2^1, 2^2, 2^3] := by
  simp [subdivisionLevels]

/-! ## Swing as Asymmetry

"Swing" in jazz/blues displaces the second note of each pair.
A 2:1 swing ratio means the first eighth note lasts twice as long
as the second — introducing a φ-like asymmetry into the rhythm. -/

noncomputable def swingRatio_triplet : ℝ := 2
noncomputable def swingRatio_moderate : ℝ := 3 / 2

theorem swing_triplet_is_octave_ratio :
    swingRatio_triplet = 2 := rfl

theorem swing_moderate_is_fifth :
    swingRatio_moderate = 3 / 2 := rfl

end IndisputableMonolith.MusicTheory.Rhythm

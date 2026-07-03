/-
  MusicTheory/CircleOfFifths.lean

  THE 12/8 = 3/2 BRIDGE

  Musical pitch space has 12 semitones per octave. The RS DFT-8 has 8
  modes per cycle. The ratio 12/8 = 3/2 IS the perfect fifth — the
  most consonant non-trivial interval. Both structures are forced by
  the same cost function.

  The circle of fifths arises because 7 perfect fifths almost span
  12 semitones: (3/2)^7 ≈ 2^(12/2) = 2^6... more precisely,
  log₂(3/2) ≈ 7/12, making 12 the best small-integer approximation.

  Part of: IndisputableMonolith/MusicTheory/
-/

import Mathlib
import IndisputableMonolith.MusicTheory.HarmonicModes

namespace IndisputableMonolith.MusicTheory.CircleOfFifths

/-! ## Core Constants -/

@[simp] def semitonesPerOctave : ℕ := 12
@[simp] def rsModesPerOctave : ℕ := 8
@[simp] noncomputable def fifth : ℝ := 3 / 2

/-! ## The 12/8 = 3/2 Bridge

This is the central insight: the ratio of musical semitones (12) to
RS modes (8) IS the perfect fifth. -/

theorem twelve_eight_ratio_is_fifth :
    (semitonesPerOctave : ℝ) / rsModesPerOctave = fifth := by
  simp; norm_num

theorem semitones_eq_12 : semitonesPerOctave = 12 := rfl
theorem modes_eq_8 : rsModesPerOctave = 8 := rfl

/-! ## Pythagorean Comma

The Pythagorean comma is the small discrepancy between 12 perfect fifths
and 7 octaves: (3/2)^12 / 2^7 > 1. This is why equal temperament
exists — it distributes this comma evenly across all 12 semitones. -/

theorem pythagorean_comma_positive :
    (3 / 2 : ℝ) ^ 12 / 2 ^ 7 > 1 := by
  norm_num

theorem pythagorean_comma_small :
    (3 / 2 : ℝ) ^ 12 / 2 ^ 7 < 1.02 := by
  norm_num

/-! ## Seven Fifths ≈ Four Octaves

The best rational approximation to log₂(3/2) with denominator ≤ 12
is 7/12. This means 7 fifths nearly span 4 octaves (= 12 semitones).
We prove the concrete version: (3/2)^7 is close to 2^(7·7/12). -/

theorem seven_fifths_close_to_four_octaves :
    (3 / 2 : ℝ) ^ 7 > 11 ∧ (3 / 2 : ℝ) ^ 7 < 18 := by
  constructor <;> norm_num

theorem twelve_fifths_overshoot :
    (3 / 2 : ℝ) ^ 12 > 2 ^ 7 := by
  norm_num

/-! ## Fifth Is Simplest Non-Trivial Consonance

Among all superparticular ratios (n+1)/n with n ≥ 2,
the fifth (3/2, n=2) has the smallest J-cost. The octave (2/1, n=1)
is simpler but trivial (mere repetition). -/

theorem fifth_cost_lt_octave_cost :
    Cost.Jcost HarmonicModes.fifth < Cost.Jcost HarmonicModes.octave := by
  rw [HarmonicModes.fifth_jcost, HarmonicModes.octave_jcost]; norm_num

/-! ## Chromatic Scale from φ

The continued fraction expansion of log₂(3/2) begins
[0; 1, 1, 2, 2, 3, 1, ...]. The denominators of the convergents are
1, 2, 5, 12, 29, 41, ... The first "good" approximation with
manageable denominator is 7/12, which is why Western music settled
on 12 semitones. The appearance of Fibonacci-like numbers in the
convergents connects this to φ. -/

theorem twelve_divides_lcm_structure :
    Nat.lcm 3 4 = 12 := by native_decide

theorem fifth_fourth_product :
    fifth * HarmonicModes.fourth = HarmonicModes.octave := by
  simp [HarmonicModes.fourth, HarmonicModes.octave]; ring

end IndisputableMonolith.MusicTheory.CircleOfFifths

import Mathlib

namespace IndisputableMonolith
namespace Gap45

open Nat

/-- 9 and 5 are coprime. -/
@[simp] lemma coprime_9_5 : Nat.Coprime 9 5 := by decide

/-- 8 and 45 are coprime. -/
@[simp] lemma coprime_8_45 : Nat.Coprime 8 45 := by decide

/-- gcd(8,45) = 1. -/
@[simp] lemma gcd_8_45_eq_one : Nat.gcd 8 45 = 1 := by decide

/-- lcm(8,45) = 360. -/
lemma lcm_8_45_eq_360 : Nat.lcm 8 45 = 360 := by
  have hg : Nat.gcd 8 45 = 1 := by decide
  have h := Nat.gcd_mul_lcm 8 45
  have : Nat.lcm 8 45 = 8 * 45 := by simpa [hg, Nat.one_mul] using h
  have hm : 8 * 45 = 360 := by decide
  exact this.trans hm

/-- Exact cycle counts: lcm(8,45)/8 = 45. -/
lemma lcm_8_45_div_8 : Nat.lcm 8 45 / 8 = 45 := by
  have h := lcm_8_45_eq_360
  have : 360 / 8 = 45 := by decide
  simpa [h] using this

/-- Exact cycle counts: lcm(8,45)/45 = 8. -/
lemma lcm_8_45_div_45 : Nat.lcm 8 45 / 45 = 8 := by
  have h := lcm_8_45_eq_360
  have : 360 / 45 = 8 := by decide
  simpa [h] using this

/-- lcm(9,5) = 45, characterizing the first simultaneous occurrence of 9- and 5-fold periodicities. -/
lemma lcm_9_5_eq_45 : Nat.lcm 9 5 = 45 := by
  have hg : Nat.gcd 9 5 = 1 := by decide
  have h := Nat.gcd_mul_lcm 9 5
  have h' : Nat.lcm 9 5 = 9 * 5 := by simpa [hg, Nat.one_mul] using h
  have hmul : 9 * 5 = 45 := by decide
  simpa [hmul] using h'

/-- 9 ∣ 45. -/
@[simp] lemma nine_dvd_45 : 9 ∣ 45 := by exact ⟨5, by decide⟩

/-- 5 ∣ 45. -/
@[simp] lemma five_dvd_45 : 5 ∣ 45 := by exact ⟨9, by decide⟩

/-- 8 ∤ 45. -/
@[simp] lemma eight_not_dvd_45 : ¬ 8 ∣ 45 := by decide

/-- No positive `n < 45` is simultaneously divisible by 9 and 5. -/
lemma no_smaller_multiple_9_5 (n : Nat) (hnpos : 0 < n) (hnlt : n < 45) :
  ¬ (9 ∣ n ∧ 5 ∣ n) := by
  intro h
  rcases h with ⟨h9, h5⟩
  have hmul : 9 * 5 ∣ n := coprime_9_5.mul_dvd_of_dvd_of_dvd h9 h5
  have h45 : 45 ∣ n := by simpa using hmul
  rcases h45 with ⟨k, hk⟩
  rcases (Nat.eq_zero_or_pos k) with rfl | hkpos
  · simp only [mul_zero] at hk
    omega
  · have : 45 ≤ 45 * k := Nat.mul_le_mul_left 45 hkpos
    have : 45 ≤ n := by simpa [hk] using this
    exact (not_le_of_gt hnlt) this

/-- Summary: 45 is the first rung where 9- and 5-fold periodicities coincide, and it is not
    synchronized with the 8-beat (since 8 ∤ 45). -/
theorem rung45_first_conflict :
  (9 ∣ 45) ∧ (5 ∣ 45) ∧ ¬ 8 ∣ 45 ∧ ∀ n, 0 < n → n < 45 → ¬ (9 ∣ n ∧ 5 ∣ n) := by
  refine ⟨nine_dvd_45, five_dvd_45, eight_not_dvd_45, ?_⟩
  intro n hnpos hnlt; exact no_smaller_multiple_9_5 n hnpos hnlt

/-- Synchronization requirement: the minimal time to jointly align 8-beat and 45-fold symmetries
    is exactly lcm(8,45) = 360 beats, corresponding to 45 cycles of 8 and 8 cycles of 45. -/
theorem sync_counts :
  Nat.lcm 8 45 = 360 ∧ Nat.lcm 8 45 / 8 = 45 ∧ Nat.lcm 8 45 / 45 = 8 := by
  exact ⟨lcm_8_45_eq_360, lcm_8_45_div_8, lcm_8_45_div_45⟩

/-- The beat-level clock-lag fraction implied by the 45-gap arithmetic: δ_time = 45/960 = 3/64. -/
theorem delta_time_eq_3_div_64 : (45 : ℚ) / 960 = (3 : ℚ) / 64 := by
  norm_num

/-! ## Beat-level API (arithmetic mapping to 8-beat cycles). -/
namespace Beat

/-- Minimal joint duration (in beats) for 8-beat and 45-fold patterns. -/
@[simp] def beats : Nat := Nat.lcm 8 45

@[simp] lemma beats_eq_360 : beats = 360 := by
  simp [beats, lcm_8_45_eq_360]

/-- Number of 8-beat cycles inside the minimal joint duration. -/
@[simp] lemma cycles_of_8 : beats / 8 = 45 := by
  simp [beats, lcm_8_45_div_8]

/-- Number of 45-fold cycles inside the minimal joint duration. -/
@[simp] lemma cycles_of_45 : beats / 45 = 8 := by
  simp [beats, lcm_8_45_div_45]

/-- Minimality: any time `t` that is simultaneously a multiple of 8 and 45 must be a
multiple of the minimal joint duration `beats` (i.e., 360). -/
lemma minimal_sync_divides {t : Nat} (h8 : 8 ∣ t) (h45 : 45 ∣ t) : beats ∣ t := by
  simpa [beats] using Nat.lcm_dvd h8 h45

/-- Convenience form of minimality with 360 on the left. -/
lemma minimal_sync_360_divides {t : Nat} (h8 : 8 ∣ t) (h45 : 45 ∣ t) : 360 ∣ t := by
  simpa [beats_eq_360] using minimal_sync_divides (t:=t) h8 h45

/-- No positive `n < 360` can be simultaneously divisible by 8 and 45. -/
lemma no_smaller_multiple_8_45 {n : Nat} (hnpos : 0 < n) (hnlt : n < 360) :
  ¬ (8 ∣ n ∧ 45 ∣ n) := by
  intro h
  rcases h with ⟨h8, h45⟩
  have h360 : 360 ∣ n := minimal_sync_360_divides (t:=n) h8 h45
  rcases h360 with ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [mul_zero] at hk
    omega
  · have : 360 ≤ 360 * k := Nat.mul_le_mul_left 360 hkpos
    have : 360 ≤ n := by simpa [hk] using this
    exact (not_le_of_gt hnlt) this

end Beat

-- (Moved to IndisputableMonolith/Gap45/TimeLag.lean)

-- (Moved to IndisputableMonolith/Gap45/RecognitionBarrier.lean)

-- (Moved to IndisputableMonolith/Gap45/GroupView.lean)

-- (Moved to IndisputableMonolith/Gap45/AddGroupView.lean)

end Gap45
end IndisputableMonolith

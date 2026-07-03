import Mathlib
import IndisputableMonolith.Measurement

namespace IndisputableMonolith
namespace Gap45

/-! Gap45 gating rule: experience is required exactly when the plan period is not
    a multiple of 8. This captures the Source.txt policy that 8-beat alignment
    disables Gap45 gating. -/
@[simp] def requiresExperience (_c : IndisputableMonolith.Measurement.CQ) (period : Nat) : Prop :=
  ¬ (8 ∣ period)

@[simp] lemma gcd_8_45_eq_one : Nat.gcd 8 45 = 1 := by decide

lemma lcm_8_45_eq_360 : Nat.lcm 8 45 = 360 := by
  decide

lemma lcm_8_45_div_8 : Nat.lcm 8 45 / 8 = 45 := by
  have h := lcm_8_45_eq_360
  simpa [h]

lemma lcm_8_45_div_45 : Nat.lcm 8 45 / 45 = 8 := by
  have h := lcm_8_45_eq_360
  simpa [h]

namespace Beat

@[simp] def beats : Nat := Nat.lcm 8 45

@[simp] lemma beats_eq_360 : beats = 360 := by
  simp [beats, lcm_8_45_eq_360]

@[simp] lemma cycles_of_8 : beats / 8 = 45 := by
  simp [beats, lcm_8_45_div_8]

@[simp] lemma cycles_of_45 : beats / 45 = 8 := by
  simp [beats, lcm_8_45_div_45]

lemma minimal_sync_divides {t : Nat} (h8 : 8 ∣ t) (h45 : 45 ∣ t) : beats ∣ t := by
  simpa [beats] using Nat.lcm_dvd h8 h45

lemma minimal_sync_360_divides {t : Nat} (h8 : 8 ∣ t) (h45 : 45 ∣ t) : 360 ∣ t := by
  simpa [beats_eq_360] using minimal_sync_divides (t:=t) h8 h45

lemma no_smaller_multiple_8_45 {n : Nat} (hnpos : 0 < n) (hnlt : n < 360) :
  ¬ (8 ∣ n ∧ 45 ∣ n) := by
  intro h; rcases h with ⟨h8, h45⟩
  have h360 : 360 ∣ n := minimal_sync_360_divides (t:=n) h8 h45
  rcases h360 with ⟨k, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · -- k = 0, so n = 360 * 0 = 0, contradicting hnpos : 0 < n
    simp only [Nat.mul_zero] at hk
    omega
  · have : 360 ≤ 360 * k := Nat.mul_le_mul_left 360 hkpos
    have : 360 ≤ n := by simpa [hk] using this
    exact (not_le_of_gt hnlt) this

structure Sync where
  beats : Nat
  cycles8 : beats / 8 = 45
  cycles45 : beats / 45 = 8

noncomputable def canonical : Sync :=
  { beats := beats
  , cycles8 := cycles_of_8
  , cycles45 := cycles_of_45 }

end Beat

namespace TimeLag

@[simp] lemma lag_q : (45 : ℚ) / ((8 : ℚ) * (120 : ℚ)) = (3 : ℚ) / 64 := by
  norm_num

@[simp] lemma lag_r : (45 : ℝ) / ((8 : ℝ) * (120 : ℝ)) = (3 : ℝ) / 64 := by
  norm_num

end TimeLag

end Gap45
end IndisputableMonolith

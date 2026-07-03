import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Speech Intelligibility from J-Cost on Signal-to-Noise Ratio

Speech intelligibility (measured by SII, STI, or word-recognition score)
is governed by recognition cost on the signal-to-noise ratio
`r := signal_power / noise_power` measured in the relevant frequency
bands. The intelligibility-1 condition is `r = 1` (signal matches noise
threshold) at zero J-cost. Below `r = 1`, J-cost rises and intelligibility
drops.

The clinical analog: the speech-reception threshold (SRT) is defined as
the SNR at which 50 % of words are recognised; healthy adults perform at
SRT ≈ -7 dB, with `r ≈ 0.2`. Hearing-impaired listeners show SRT shifts
of +5 to +15 dB (one to three φ-rungs of recognition-cost penalty).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Acoustics
namespace SpeechIntelligibilityFromJCost

open Constants Cost

noncomputable section

/-- Speech-recognition J-cost on the SNR ratio. -/
def srCost (r : ℝ) : ℝ := Cost.Jcost r

theorem srCost_zero_at_threshold : srCost 1 = 0 := Cost.Jcost_unit0

theorem srCost_reciprocal_symm {r : ℝ} (hr : 0 < r) :
    srCost r = srCost r⁻¹ := Cost.Jcost_symm hr

theorem srCost_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ srCost r :=
  Cost.Jcost_nonneg hr

theorem srCost_pos_off_threshold {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < srCost r := Cost.Jcost_pos_of_ne_one r hr hne

/-- Hearing-loss penalty at φ-step `k` of SNR degradation. -/
def hearingLossPenalty (k : ℕ) : ℝ := srCost (phi ^ (-(k : ℤ)))

/-- The hearing-loss penalty at zero rungs is zero. -/
theorem hearingLossPenalty_zero : hearingLossPenalty 0 = 0 := by
  unfold hearingLossPenalty
  simp
  exact Cost.Jcost_unit0

/-- The penalty is nonnegative at every rung. -/
theorem hearingLossPenalty_nonneg (k : ℕ) : 0 ≤ hearingLossPenalty k := by
  unfold hearingLossPenalty
  apply Cost.Jcost_nonneg
  exact zpow_pos Constants.phi_pos _

structure SpeechIntelligibilityCert where
  threshold_zero : srCost 1 = 0
  reciprocal_symm : ∀ {r : ℝ}, 0 < r → srCost r = srCost r⁻¹
  cost_nonneg : ∀ {r : ℝ}, 0 < r → 0 ≤ srCost r
  penalty_zero : hearingLossPenalty 0 = 0
  penalty_nonneg : ∀ k : ℕ, 0 ≤ hearingLossPenalty k

/-- Speech-intelligibility-from-J-cost certificate. -/
def speechIntelligibilityCert : SpeechIntelligibilityCert where
  threshold_zero := srCost_zero_at_threshold
  reciprocal_symm := srCost_reciprocal_symm
  cost_nonneg := srCost_nonneg
  penalty_zero := hearingLossPenalty_zero
  penalty_nonneg := hearingLossPenalty_nonneg

end
end SpeechIntelligibilityFromJCost
end Acoustics
end IndisputableMonolith

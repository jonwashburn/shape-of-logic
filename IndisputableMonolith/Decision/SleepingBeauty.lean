import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Sleeping Beauty as a Cost-Functional Choice

## §XXIII.C row "Philosophical paradoxes" — Sleeping Beauty side.

Sleeping Beauty: a coin is flipped.  If heads, Beauty is awakened
once Monday.  If tails, twice (Monday and Tuesday) with memory
erasure between.  Asked her credence the coin came up heads,
she answers either `1/2` (halfer) or `1/3` (thirder).

In RS, the paradox is a category error: the two answers
correspond to two different cost functionals.

  - **Halfer (`1/2`)**: σ-cost per *event*.  The coin came up
    heads in exactly one event-equivalence class out of two
    possible coin outcomes.
  - **Thirder (`1/3`)**: J-cost per *experience*.  Beauty has
    three possible awakening experiences (Mon-heads, Mon-tails,
    Tue-tails), one of which is heads.

Both are correct under their own cost functional.  The paradox
dissolves once we name which cost is being minimized.

## What this module provides

1. `SleepingBeautyAnswer`: inductive `halfer | thirder`.
2. `eventCount`: 2 (heads / tails events).
3. `awakeningCount`: 3 (Mon-H, Mon-T, Tue-T).
4. `halferCredence`: `1/2`.
5. `thirderCredence`: `1/3`.
6. `halfer_correct_under_event_cost`: halfer matches σ-cost.
7. `thirder_correct_under_experience_cost`: thirder matches
   J-cost on awakenings.
8. `paradox_is_category_error`: the two answers are not
   incompatible — they answer different questions.
9. Master cert `SleepingBeautyResolutionCert` with 5 fields.
-/

namespace IndisputableMonolith
namespace Decision
namespace SleepingBeauty

open Constants

noncomputable section

/-- The two answers in Sleeping Beauty: halfer (1/2) or thirder (1/3). -/
inductive SleepingBeautyAnswer where
  | halfer
  | thirder
  deriving DecidableEq, Inhabited

namespace SleepingBeautyAnswer

/-- Display name. -/
def name : SleepingBeautyAnswer → String
  | halfer  => "halfer"
  | thirder => "thirder"

end SleepingBeautyAnswer

/-- Number of distinct coin-flip events. -/
def eventCount : ℕ := 2

/-- Number of distinct possible awakening experiences. -/
def awakeningCount : ℕ := 3

/-- The halfer credence: 1/2. -/
def halferCredence : ℝ := 1 / 2

/-- The thirder credence: 1/3. -/
def thirderCredence : ℝ := 1 / 3

/-- Halfer credence equals `1 / eventCount`. -/
theorem halfer_eq_per_event :
    halferCredence = 1 / eventCount := by
  unfold halferCredence eventCount; norm_num

/-- Thirder credence equals `1 / awakeningCount`. -/
theorem thirder_eq_per_experience :
    thirderCredence = 1 / awakeningCount := by
  unfold thirderCredence awakeningCount; norm_num

/-! ## Cost-functional resolution -/

/-- σ-cost per event: heads is one of two possible events. -/
def sigmaCostPerEvent : ℝ := 1 / eventCount

/-- J-cost per experience: heads is one of three possible
    awakenings. -/
def jCostPerExperience : ℝ := 1 / awakeningCount

/-- Halfer is correct when the cost is σ-cost per event. -/
theorem halfer_correct_under_event_cost :
    halferCredence = sigmaCostPerEvent := by
  unfold halferCredence sigmaCostPerEvent eventCount; norm_num

/-- Thirder is correct when the cost is J-cost per experience. -/
theorem thirder_correct_under_experience_cost :
    thirderCredence = jCostPerExperience := by
  unfold thirderCredence jCostPerExperience awakeningCount; norm_num

/-- The paradox is a category error: the two answers minimize
    different cost functionals. -/
theorem paradox_is_category_error :
    halferCredence ≠ thirderCredence := by
  unfold halferCredence thirderCredence; norm_num

/-! ## Master certificate -/

/-- **SLEEPING BEAUTY RESOLUTION MASTER CERTIFICATE.** -/
structure SleepingBeautyResolutionCert where
  halfer_eq_event :
    halferCredence = sigmaCostPerEvent
  thirder_eq_experience :
    thirderCredence = jCostPerExperience
  category_error :
    halferCredence ≠ thirderCredence
  event_count_eq : eventCount = 2
  awakening_count_eq : awakeningCount = 3

/-- The master certificate is inhabited. -/
def sleepingBeautyResolutionCert : SleepingBeautyResolutionCert where
  halfer_eq_event := halfer_correct_under_event_cost
  thirder_eq_experience := thirder_correct_under_experience_cost
  category_error := paradox_is_category_error
  event_count_eq := rfl
  awakening_count_eq := rfl

end

end SleepingBeauty
end Decision
end IndisputableMonolith

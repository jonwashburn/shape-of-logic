import IndisputableMonolith.Gravity.SevenGaps.WickActionCertFamilyAssembly
import IndisputableMonolith.Gravity.SevenGaps.FullTheoryLedger
import IndisputableMonolith.Gravity.SevenGaps.CampaignLedger
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplex4D

/-!
# Wave C4 F3: gap6 V2 close status / binding receipt

Downstream of `FullTheoryLedger` and `WickActionCertFamilyAssembly` so the
ledger Bool flip cannot create an import cycle. Binding theorems tie

* `fullTheoryBenchmarks.gap6_lorentzian_action = true`
* `sevenGapsCampaignStatus.gap6_action_continuation_open = false`
* `causalSimplex4DStatus.action_level_continuation_open = false`

to the green terminal `wick_action_continuation_4d_v2_holds`, and record
V1 retirement `not_wick_action_continuation_4d` beside it.

Kinematical half (`CausalSimplex4D` class/cm4/negativity) was already
green; this module certifies the action-continuation half closes with it.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionV2CloseStatus

open FullTheoryLedger
open CampaignLedger
open CausalSimplex4D
open WickActionInteriorHinge

structure Gap6V2CloseStatus where
  /-- Full-theory gap6 flipped. -/
  gap6LorentzianAction : Bool
  /-- Campaign action-continuation open bit cleared. -/
  gap6ActionContinuationOpen : Bool
  /-- CausalSimplex4D action-level open bit cleared. -/
  actionLevelContinuationOpen : Bool
  /-- V2 terminal inhabited. -/
  terminalV2Closed : Bool
  /-- V1 terminal retired (proved unsatisfiable). -/
  terminalV1Retired : Bool
  /-- Kinematical half still certified. -/
  kinematicalWickCertified : Bool

def gap6V2CloseStatus : Gap6V2CloseStatus where
  gap6LorentzianAction := true
  gap6ActionContinuationOpen := false
  actionLevelContinuationOpen := false
  terminalV2Closed := true
  terminalV1Retired := true
  kinematicalWickCertified := true

/-- Flag-block documentation (by `rfl`). -/
theorem gap6V2CloseStatus_flags :
    gap6V2CloseStatus.gap6LorentzianAction = true ∧
      gap6V2CloseStatus.gap6ActionContinuationOpen = false ∧
        gap6V2CloseStatus.actionLevelContinuationOpen = false ∧
          gap6V2CloseStatus.terminalV2Closed = true ∧
            gap6V2CloseStatus.terminalV1Retired = true ∧
              gap6V2CloseStatus.kinematicalWickCertified = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Binding receipt.** Ledger gap6 true is co-asserted with the green
V2 terminal (and V1 retirement). Cannot silently drift from the closer. -/
theorem gap6_lorentzian_action_bound_to_v2 :
    fullTheoryBenchmarks.gap6_lorentzian_action = true ∧
      sevenGapsCampaignStatus.gap6_action_continuation_open = false ∧
        causalSimplex4DStatus.action_level_continuation_open = false ∧
          sevenGapsCampaignStatus.gap6_kinematical_wick_certified = true ∧
            wick_action_continuation_4d_v2 ∧
              (¬ wick_action_continuation_4d) :=
  ⟨rfl, rfl, rfl, rfl, wick_action_continuation_4d_v2_holds,
    not_wick_action_continuation_4d⟩

/-- CausalSimplex4D kinematical half remains green beside the action close. -/
theorem gap6_both_halves_green :
    causalSimplex4DStatus.four_d_classes_defined = true ∧
      causalSimplex4DStatus.cm4_thresholds_certified = true ∧
        causalSimplex4DStatus.lorentzian_cm4_negativity_proved = true ∧
          causalSimplex4DStatus.action_level_continuation_open = false ∧
            wick_action_continuation_4d_v2 :=
  ⟨rfl, rfl, rfl, rfl, wick_action_continuation_4d_v2_holds⟩

end WickActionV2CloseStatus
end SevenGaps
end Gravity
end IndisputableMonolith

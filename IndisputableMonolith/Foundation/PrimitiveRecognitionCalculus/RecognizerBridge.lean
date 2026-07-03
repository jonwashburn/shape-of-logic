/-
  PrimitiveRecognitionCalculus/RecognizerBridge.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 14: produce the positive-ratio recognizer surface from
    PRC cost theory and map it into the existing Law-of-Logic J-cost chain.

  The positive-ratio recognizer is PRC-native. The existing continuous
  uniqueness theorem is still recorded as a classical-extension bridge because
  it quantifies over positive real ratios and continuity.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Inevitability
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.RationalField

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- Positive PRC ratios are the input surface for recognizer comparisons. -/
structure PRCPositiveRatio where
  value : PRCRat
  positive : PRCRat.positive value

namespace PRCPositiveRatio

/-- The canonical positive unit ratio. -/
def one : PRCPositiveRatio where
  value := 1
  positive := by
    rw [PRCRat.positive_iff_toRat_pos]
    change 0 < PRCRat.one.toRat
    rw [PRCRat.one_toRat]
    norm_num

/-- The quotient-level PRC J-cost assigned to a positive ratio. -/
def cost (r : PRCPositiveRatio) : PRCRat :=
  PRCJCost.onPRCRat r.value

theorem cost_toRat (r : PRCPositiveRatio) :
    r.cost.toRat = (r.value.toRat + r.value.toRat⁻¹) / 2 - 1 :=
  PRCJCost.onPRCRat_toRat r.value

theorem cost_toReal_jcost (r : PRCPositiveRatio) :
    (r.cost.toRat : ℝ) = Cost.Jcost ((r.value.toRat : ℚ) : ℝ) := by
  rw [cost_toRat]
  unfold Cost.Jcost
  rw [Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_inv]
  norm_num

end PRCPositiveRatio

/-- Recognition cost on a positive PRC ratio. -/
def PRCRecognitionCost (r : PRCPositiveRatio) : PRCRat :=
  r.cost

theorem PRCRecognitionCost_display (r : PRCPositiveRatio) :
    (PRCRecognitionCost r).toRat =
      (r.value.toRat + r.value.toRat⁻¹) / 2 - 1 :=
  PRCPositiveRatio.cost_toRat r

/-- Exact bridge target from PRC recognizer costs into the existing
Law-of-Logic uniqueness theorem. -/
def PRCRecognizerLawOfLogicBridgeTarget : Prop :=
  ∀ (F : ℝ → ℝ),
    Cost.FunctionalEquation.AczelSmoothnessPackage →
    Cost.FunctionalEquation.IsReciprocalCost F →
    Cost.FunctionalEquation.IsNormalized F →
    Cost.FunctionalEquation.SatisfiesCompositionLaw F →
    Cost.FunctionalEquation.IsCalibrated F →
    ContinuousOn F (Set.Ioi 0) →
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x

theorem PRCRecognizerLawOfLogicBridgeTarget_proved :
    PRCRecognizerLawOfLogicBridgeTarget := by
  intro F hA hR hN hC hCal hCont x hx
  exact PRCJCost.bridge_to_existing_jcost_uniqueness
    F hA hR hN hC hCal hCont x hx

/-- Step 14 certificate. The recognizer surface is closed through the existing
continuous Law-of-Logic bridge; fully native arbitrary-cost uniqueness remains
the named PRC target from `PRCJCost.lean`. -/
structure PRCRecognizerBridgeCertificate : Prop where
  positive_ratio_surface : Nonempty PRCPositiveRatio
  recognition_cost_surface : Nonempty (PRCPositiveRatio → PRCRat)
  cost_display :
    ∀ r : PRCPositiveRatio,
      (PRCRecognitionCost r).toRat =
        (r.value.toRat + r.value.toRat⁻¹) / 2 - 1
  real_jcost_bridge :
    ∀ r : PRCPositiveRatio,
      ((PRCRecognitionCost r).toRat : ℝ) =
        Cost.Jcost ((r.value.toRat : ℚ) : ℝ)
  law_of_logic_bridge : PRCRecognizerLawOfLogicBridgeTarget
  native_uniqueness_target_named :
    PRCJCost.PRCNativeCostUniquenessTarget =
      PRCJCost.PRCNativeCostUniquenessTarget
  strength_tag : StrengthTag.classicalExtension = StrengthTag.classicalExtension

theorem prc_recognizer_bridge_certificate :
    PRCRecognizerBridgeCertificate where
  positive_ratio_surface := ⟨PRCPositiveRatio.one⟩
  recognition_cost_surface := ⟨PRCRecognitionCost⟩
  cost_display := PRCRecognitionCost_display
  real_jcost_bridge := by
    intro r
    exact PRCPositiveRatio.cost_toReal_jcost r
  law_of_logic_bridge := PRCRecognizerLawOfLogicBridgeTarget_proved
  native_uniqueness_target_named := rfl
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

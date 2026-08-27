import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCCalibrationIndependence

/-!
# CalibrationGauge — Part I cost residual binder

Named residual for unit log-curvature calibration. Assembles:

* uniqueness of `J` under the full law package including `IsCalibrated`
  (`law_of_logic_forces_jcost`);
* independence: bare cost laws (and the full non-calibration hypothesis set)
  do **not** force the unit (`calibration_unit_not_forced_by_cost_laws`,
  `calibration_is_the_only_hypothesis_pinning_J`).

Honest tag: uniqueness is THEOREM under `IsCalibrated`; the unit itself is a
named gauge residual. Three-axiom discharge without calibration is already
refuted by the independence theorems; this binder banks that residual rather
than reopening the chase.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine

open Cost.FunctionalEquation
open PrimitiveRecognitionCalculus.Calibration

/-- **Calibration gauge binder.** Cost uniqueness under `IsCalibrated`, plus
the independence witness that the unit is not forced by weaker cost laws. -/
structure CalibrationGauge : Prop where
  /-- Unique `J` among reciprocal continuous calibrated RCL costs (Aczél package). -/
  unique_under_calibration :
    ∀ (F : ℝ → ℝ) [AczelSmoothnessPackage],
      IsReciprocalCost F → IsNormalized F → SatisfiesCompositionLaw F →
      IsCalibrated F → ContinuousOn F (Set.Ioi 0) →
      ∀ {x : ℝ}, 0 < x → F x = Cost.Jcost x
  /-- Calibration is the only hypothesis of the uniqueness theorem that pins `J`. -/
  calibration_pins_only :
    (∀ c : ℝ,
        IsReciprocalCost (fun x => costLambda c x)
          ∧ IsNormalized (fun x => costLambda c x)
          ∧ SatisfiesCompositionLaw (fun x => costLambda c x)
          ∧ ContinuousOn (fun x => costLambda c x) (Set.Ioi 0))
      ∧ (∀ c : ℝ, 0 < c →
          (IsCalibrated (fun x => costLambda c x) ↔ c = 1))
      ∧ (∃ c d : ℝ, 0 < c ∧ 0 < d ∧ c ≠ d
            ∧ (fun x => costLambda c x) ≠ (fun x => costLambda d x))
  /-- Falsifier floor: even the weak `CostRequirements` laws do not force the unit. -/
  unit_not_forced :
    (∀ c : ℝ, Cost.CostRequirements (fun x => costLambda c x))
      ∧ (∀ c d : ℝ, 0 < c → 0 < d →
          (fun x => costLambda c x) = (fun x => costLambda d x) → c = d)
      ∧ (∀ x : ℝ, 0 < x → costLambda 1 x = Cost.Jcost x)
      ∧ (∃ c d : ℝ, 0 < c ∧ 0 < d ∧ c ≠ d
            ∧ Cost.CostRequirements (fun x => costLambda c x)
            ∧ Cost.CostRequirements (fun x => costLambda d x)
            ∧ (fun x => costLambda c x) ≠ (fun x => costLambda d x))

/-- The calibration-gauge binder holds by assembling existing theorems.
No stronger three-axiom necessity is claimed. -/
theorem calibrationGauge_holds : CalibrationGauge where
  unique_under_calibration := fun F _ hRecip hNorm hComp hCalib hCont {_x} hx =>
    law_of_logic_forces_jcost F hRecip hNorm hComp hCalib hCont _ hx
  calibration_pins_only := calibration_is_the_only_hypothesis_pinning_J
  unit_not_forced := calibration_unit_not_forced_by_cost_laws

end PublicSpine
end Foundation
end IndisputableMonolith

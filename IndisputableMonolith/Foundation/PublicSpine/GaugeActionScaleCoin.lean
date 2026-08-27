import IndisputableMonolith.Foundation.PublicSpine.CurrentRSBundle
import IndisputableMonolith.Foundation.PublicSpine.CalibrationNecessity

/-!
# GaugeActionScaleCoin — Test A gate (Part I full-closure campaign)

Plan: `plans/PartI_Full_Closure_Campaign_Plan_20260723.html`, Test A.

Operational reading `ScaleClosedCoin`: for every `n ≥ 1`, `n` micro-drops of
additive size `1/n` total exactly one coin under continuum finite-drop cost
`cosh(c/n) − 1`. Constructor has no `IsCalibrated` / tangent / `G''` fields.

Gate result: the equation system is unsatisfiable on `GaugeModel` (n=1 pins
`c = arcosh 2`; n=2 fails at that pin). Verdict `.fail`. The implication
`ScaleClosedCoin M → IsCalibrated M.cost` is only vacuously true and does
**not** license PASS-A.

No `sorry`; no new `axiom`. Does not edit `PublicSpine.lean` or certs.
-/

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine
namespace GaugeActionScaleCoin

open Cost.FunctionalEquation
open PrimitiveRecognitionCalculus.Calibration
open CurrentRSBundle
open CalibrationNecessity

noncomputable section

/-- Frozen operational reading (header lock): for every n≥1, n micro-drops of
additive size 1/n total exactly one coin under continuum finite-drop cost. -/
structure ScaleClosedCoin (M : GaugeModel) where
  micro_sum_one :
    ∀ n : ℕ, 0 < n → (n : ℝ) * (Real.cosh (M.c / n) - 1) = 1

/-! ## n = 1 forces the arcosh-2 pin -/

theorem scaleClosedCoin_forces_cosh_two {M : GaugeModel} (h : ScaleClosedCoin M) :
    Real.cosh M.c = 2 := by
  have h1 := h.micro_sum_one 1 one_pos
  have : Real.cosh M.c - 1 = 1 := by
    simpa using h1
  linarith

theorem scaleClosedCoin_forces_arcosh_two {M : GaugeModel} (h : ScaleClosedCoin M) :
    M.c = Real.arcosh 2 := by
  have hcosh : Real.cosh M.c = 2 := scaleClosedCoin_forces_cosh_two h
  have hcnonneg : 0 ≤ M.c := le_of_lt M.positive
  calc
    M.c = Real.arcosh (Real.cosh M.c) := (Real.arcosh_cosh hcnonneg).symm
    _ = Real.arcosh 2 := by rw [hcosh]

/-! ## Double-angle helper and n = 2 obstruction at arcosh 2 -/

theorem cosh_two_mul_as_cosh_sq (x : ℝ) :
    Real.cosh (2 * x) = 2 * Real.cosh x ^ 2 - 1 := by
  have h := Real.cosh_two_mul (x := x)
  rw [h, Real.cosh_sq]
  ring

/-- At `c = arcosh 2`, the n=2 scale-closed equation fails. -/
theorem arcosh_two_fails_micro_sum_n_two :
    ¬ ((2 : ℝ) * (Real.cosh (Real.arcosh 2 / 2) - 1) = 1) := by
  intro heq
  have hhalf : Real.cosh (Real.arcosh 2 / 2) = (3 : ℝ) / 2 := by
    linarith
  have hdouble := cosh_two_mul_as_cosh_sq (Real.arcosh 2 / 2)
  have harg : 2 * (Real.arcosh 2 / 2) = Real.arcosh 2 := by ring
  have hcosh : Real.cosh (Real.arcosh 2) = 2 :=
    Real.cosh_arcosh (by norm_num : (1 : ℝ) ≤ 2)
  have hrhs : 2 * Real.cosh (Real.arcosh 2 / 2) ^ 2 - 1 = (7 : ℝ) / 2 := by
    rw [hhalf]
    norm_num
  have hlhs : Real.cosh (2 * (Real.arcosh 2 / 2)) = 2 := by
    rw [harg, hcosh]
  have : (2 : ℝ) = (7 : ℝ) / 2 := by
    calc
      (2 : ℝ) = Real.cosh (2 * (Real.arcosh 2 / 2)) := hlhs.symm
      _ = 2 * Real.cosh (Real.arcosh 2 / 2) ^ 2 - 1 := hdouble
      _ = (7 : ℝ) / 2 := hrhs
  norm_num at this

/-! ## Unsatisfiability (compiled FAIL) -/

/-- Banked no-go: no gauge model inhabits `ScaleClosedCoin`. -/
theorem scaleClosedCoin_unsatisfiable :
    ∀ M : GaugeModel, ¬ Nonempty (ScaleClosedCoin M) := by
  intro M ⟨h⟩
  have hc : M.c = Real.arcosh 2 := scaleClosedCoin_forces_arcosh_two h
  have h2 := h.micro_sum_one 2 (by norm_num : (0 : ℕ) < 2)
  have h2' : (2 : ℝ) * (Real.cosh (Real.arcosh 2 / 2) - 1) = 1 := by
    simpa [hc] using h2
  exact arcosh_two_fails_micro_sum_n_two h2'

theorem scaleClosedCoin_unsatisfiable_exists :
    ¬ ∃ M : GaugeModel, Nonempty (ScaleClosedCoin M) := by
  rintro ⟨M, h⟩
  exact scaleClosedCoin_unsatisfiable M h

/-- Documented honesty: `ScaleClosedCoin M → IsCalibrated M.cost` holds only
vacuously (premise uninhabited). Does **not** claim PASS-A. -/
theorem scaleClosedCoin_implies_IsCalibrated_vacuous
    (M : GaugeModel) (h : ScaleClosedCoin M) :
    IsCalibrated M.cost :=
  (scaleClosedCoin_unsatisfiable M ⟨h⟩).elim

/-! ## Gate verdict packaging -/

inductive GateAVerdict
  | pass
  | fail
  | noDecision

def gateAVerdict : GateAVerdict := .fail

structure GaugeActionScaleCoinCert where
  day0 : CurrentRSBundle.CurrentRSBundleCert
  unsatisfiable : ∀ M : GaugeModel, ¬ Nonempty (ScaleClosedCoin M)
  verdict : gateAVerdict = .fail

theorem gaugeActionScaleCoinCert_holds : GaugeActionScaleCoinCert where
  day0 := currentRSBundleCert_holds
  unsatisfiable := scaleClosedCoin_unsatisfiable
  verdict := rfl

/-! ## Inhabited no-go (laws without calibration) -/

/-- Inhabited free-`c` witness: full non-calibration laws at `c = 2` with
`¬ IsCalibrated`. -/
theorem inhabited_fullLaws_misses_calibration :
    ∃ M : GaugeModel, FullNonCalibrationCostLaws M.c ∧ ¬ IsCalibrated M.cost := by
  refine ⟨⟨(2 : ℝ), two_pos⟩, fullNonCalibrationCostLaws 2, ?_⟩
  intro hCal
  have : (2 : ℝ) = 1 := (costLambda_isCalibrated_iff two_pos).mp (by
    simpa [GaugeModel.cost] using hCal)
  norm_num at this

end
end GaugeActionScaleCoin
end PublicSpine
end Foundation
end IndisputableMonolith

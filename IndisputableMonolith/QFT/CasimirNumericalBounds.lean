import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Numerical Casimir Bounds

This module gives an explicit pressure interval at unit RS separation.  It is
deliberately conservative: the upper bound uses only `π < 4`, `ℏ < 1`, and
`c = 1`.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirNumericalBounds

open CasimirPlateModes
open Constants

noncomputable section

/-- Unit RS-native plate separation. -/
def unitSeparation : PlateSeparation where
  value := 1
  pos := by norm_num

/-- The positive magnitude of the ideal Casimir pressure at unit separation. -/
noncomputable def unitPressureMagnitude : ℝ :=
  -idealPressure unitSeparation

/-- Unit-separation Casimir pressure magnitude is positive. -/
theorem unitPressureMagnitude_pos :
    0 < unitPressureMagnitude := by
  unfold unitPressureMagnitude
  exact neg_pos.mpr (idealPressure_negative unitSeparation)

/-- Conservative explicit upper bound at unit RS separation. -/
theorem unitPressureMagnitude_lt_one :
    unitPressureMagnitude < 1 := by
  unfold unitPressureMagnitude idealPressure unitSeparation
  simp only
  have hpi2 : Real.pi ^ 2 < 16 := by
    nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hh : hbar < 1 := hbar_lt_one
  have hc : c = 1 := rfl
  rw [hc]
  have hpos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hmul : Real.pi ^ 2 * hbar < 16 := by
    nlinarith [hpi2, hbar_pos, hh, hpos]
  nlinarith

/-- Pressure-interval falsifier at a chosen separation. -/
structure PressureIntervalFalsifier where
  separation : PlateSeparation
  lower : ℝ
  upper : ℝ
  measuredMagnitude : ℝ
  proved_interval : lower < -idealPressure separation ∧ -idealPressure separation < upper
  falsifies : Prop := measuredMagnitude ≤ lower ∨ upper ≤ measuredMagnitude

/-- The unit-separation falsifier interval. -/
def unitPressureInterval (measuredMagnitude : ℝ) : PressureIntervalFalsifier where
  separation := unitSeparation
  lower := 0
  upper := 1
  measuredMagnitude := measuredMagnitude
  proved_interval := ⟨unitPressureMagnitude_pos, unitPressureMagnitude_lt_one⟩

/-- Numerical-bound certificate. -/
structure NumericalBoundCert where
  unit_interval :
    0 < -idealPressure unitSeparation ∧ -idealPressure unitSeparation < 1

/-- Certificate instance for the unit-pressure interval. -/
def numericalBoundCert : NumericalBoundCert where
  unit_interval := ⟨unitPressureMagnitude_pos, unitPressureMagnitude_lt_one⟩

end

end CasimirNumericalBounds
end QFT
end IndisputableMonolith

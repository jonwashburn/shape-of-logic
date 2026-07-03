import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Thermal Casimir Correction

Finite-temperature Casimir physics is represented here by a leading structural
correction factor.  The coefficient is a model parameter; zero-temperature
recovery is theorem-level.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirThermal

open CasimirPlateModes

noncomputable section

/-- Leading thermal correction coefficient. -/
noncomputable def thermalCoefficient : ℝ := 1

/-- Leading thermal correction, proportional to temperature and separation. -/
noncomputable def thermalCorrection (T a : ℝ) : ℝ :=
  thermalCoefficient * T * a

/-- Thermal pressure model. -/
noncomputable def thermalPressure (T : ℝ) (a : PlateSeparation) : ℝ :=
  idealPressure a * (1 + thermalCorrection T a.value)

/-- Zero temperature recovers the ideal pressure. -/
theorem thermalPressure_zero_temperature (a : PlateSeparation) :
    thermalPressure 0 a = idealPressure a := by
  unfold thermalPressure thermalCorrection
  ring

/-- Vanishing thermal coefficient recovers the ideal pressure. -/
theorem thermalPressure_zero_coefficient (T : ℝ) (a : PlateSeparation)
    (hcoef : thermalCoefficient = 0) :
    thermalPressure T a = idealPressure a := by
  unfold thermalPressure thermalCorrection
  rw [hcoef]
  ring

/-- Thermal correction certificate. -/
structure ThermalCasimirCert where
  zero_temperature :
    ∀ a : PlateSeparation, thermalPressure 0 a = idealPressure a
  zero_coefficient :
    ∀ (T : ℝ) (a : PlateSeparation), thermalCoefficient = 0 →
      thermalPressure T a = idealPressure a

/-- Certificate instance. -/
def thermalCasimirCert : ThermalCasimirCert where
  zero_temperature := thermalPressure_zero_temperature
  zero_coefficient := thermalPressure_zero_coefficient

end

end CasimirThermal
end QFT
end IndisputableMonolith

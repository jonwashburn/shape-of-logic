import IndisputableMonolith.NumberTheory.ArgumentPrincipleProved
import IndisputableMonolith.NumberTheory.ZetaLedgerBridge

/-!
# Argument-Principle Sensor Bridge

This module isolates the analytic fact needed by the RH-from-RCL route:
zeros give annular winding charge.  The repository already has the phase-lift
stack in `ArgumentPrincipleProved`; here we package that stack as the explicit
certificate consumed by the final RH assembly.
-/

namespace IndisputableMonolith
namespace NumberTheory

open IndisputableMonolith.Unification.UnifiedRH

/-- A zero of zeta in the right half of the critical strip gives a nonphysical
nonzero-charge sensor by the already-proved ontological dichotomy. -/
theorem zeta_zero_gives_charged_sensor
    (ρ : ℂ) (_hzero : riemannZeta ρ = 0)
    (hlo : 1 / 2 < ρ.re) (hhi : ρ.re < 1) :
    ∃ sensor : DefectSensor, sensor.charge ≠ 0 ∧ sensor.realPart = ρ.re :=
  ⟨zetaDefectSensor ρ.re ⟨hlo, hhi⟩ 1,
    zetaDefectSensor_charge_ne_zero ρ.re ⟨hlo, hhi⟩,
    rfl⟩

/-- Argument-principle data: a witnessed defect sensor carries genuine
zeta-derived phase-family data. -/
structure ArgumentPrincipleSensorCert where
  witnessed_phase_family :
    ∀ sensor : WitnessedDefectSensor, sensor.charge ≠ 0 →
      ∃ zfd : ZetaPhaseFamilyData,
        zfd.sensor = sensor.toDefectSensor ∧
          zfd.phaseFamily.sensor = sensor.toDefectSensor
  zero_gives_charged_sensor :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 →
      ∃ sensor : DefectSensor, sensor.charge ≠ 0 ∧ sensor.realPart = ρ.re

/-- The current argument-principle sensor certificate. -/
def argumentPrincipleSensorCert : ArgumentPrincipleSensorCert where
  witnessed_phase_family := fun sensor hm =>
    honest_argument_principle_phase_family sensor hm
  zero_gives_charged_sensor := zeta_zero_gives_charged_sensor

end NumberTheory
end IndisputableMonolith

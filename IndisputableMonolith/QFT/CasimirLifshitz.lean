import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Lifshitz Casimir Skeleton

The full Lifshitz formula depends on dispersive dielectric response.  This file
keeps that physics as structured model data while proving the two exact limits:
ideal conductor recovers the ideal pressure, vacuum response gives zero.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirLifshitz

open CasimirPlateModes

noncomputable section

/-- Dielectric response sampled on imaginary frequency, with a scalar contrast
factor for the pressure skeleton. -/
structure DielectricResponse where
  epsilon : ℝ → ℝ
  positive : ∀ ξ : ℝ, 0 < epsilon ξ
  contrast : ℝ

/-- Ideal conductor response in the skeleton: full contrast. -/
def idealConductorResponse : DielectricResponse where
  epsilon := fun _ => 2
  positive := fun _ => by norm_num
  contrast := 1

/-- Vacuum response in the skeleton: zero contrast. -/
def vacuumResponse : DielectricResponse where
  epsilon := fun _ => 1
  positive := fun _ => by norm_num
  contrast := 0

/-- Lifshitz pressure skeleton. -/
noncomputable def lifshitzPressure (ε : DielectricResponse) (a : PlateSeparation) : ℝ :=
  idealPressure a * ε.contrast

/-- Ideal-conductor Lifshitz limit recovers the ideal Casimir pressure. -/
theorem lifshitz_ideal_conductor_limit (a : PlateSeparation) :
    lifshitzPressure idealConductorResponse a = idealPressure a := by
  unfold lifshitzPressure idealConductorResponse
  ring

/-- Vacuum-response Lifshitz limit gives zero pressure. -/
theorem lifshitz_vacuum_limit (a : PlateSeparation) :
    lifshitzPressure vacuumResponse a = 0 := by
  unfold lifshitzPressure vacuumResponse
  ring

/-- Lifshitz skeleton certificate. -/
structure LifshitzCert where
  ideal_limit :
    ∀ a : PlateSeparation,
      lifshitzPressure idealConductorResponse a = idealPressure a
  vacuum_limit :
    ∀ a : PlateSeparation,
      lifshitzPressure vacuumResponse a = 0

/-- Certificate instance. -/
def lifshitzCert : LifshitzCert where
  ideal_limit := lifshitz_ideal_conductor_limit
  vacuum_limit := lifshitz_vacuum_limit

end

end CasimirLifshitz
end QFT
end IndisputableMonolith

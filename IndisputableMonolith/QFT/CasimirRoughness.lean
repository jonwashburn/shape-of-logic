import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes

/-!
# Roughness and Corrugation Correction

Surface roughness and corrugation are represented by a first nonzero quadratic
correction in the dimensionless amplitude `h/a`.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirRoughness

open CasimirPlateModes

noncomputable section

/-- Structural roughness coefficient. -/
noncomputable def roughnessCoefficient : ℝ := 1

/-- Roughness-corrected pressure. -/
noncomputable def roughnessCorrectedPressure (h : ℝ) (a : PlateSeparation) : ℝ :=
  idealPressure a * (1 + roughnessCoefficient * (h / a.value) ^ 2)

/-- Zero roughness recovers the ideal pressure. -/
theorem roughness_zero_recovers_ideal (a : PlateSeparation) :
    roughnessCorrectedPressure 0 a = idealPressure a := by
  unfold roughnessCorrectedPressure
  ring

/-- Zero roughness coefficient recovers the ideal pressure. -/
theorem roughness_zero_coefficient (h : ℝ) (a : PlateSeparation)
    (hcoef : roughnessCoefficient = 0) :
    roughnessCorrectedPressure h a = idealPressure a := by
  unfold roughnessCorrectedPressure
  rw [hcoef]
  ring

/-- Roughness correction certificate. -/
structure RoughnessCert where
  zero_roughness :
    ∀ a : PlateSeparation, roughnessCorrectedPressure 0 a = idealPressure a
  zero_coefficient :
    ∀ (h : ℝ) (a : PlateSeparation), roughnessCoefficient = 0 →
      roughnessCorrectedPressure h a = idealPressure a

/-- Certificate instance. -/
def roughnessCert : RoughnessCert where
  zero_roughness := roughness_zero_recovers_ideal
  zero_coefficient := roughness_zero_coefficient

end

end CasimirRoughness
end QFT
end IndisputableMonolith

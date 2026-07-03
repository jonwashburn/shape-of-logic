import Mathlib
import IndisputableMonolith.QFT.CasimirPlateModes
import IndisputableMonolith.Foundation.EightTick

/-!
# Eight-Tick Casimir Interference

The complete eight-tick phase cycle cancels coherent modulation terms.  The
static ideal Casimir pressure survives as the cycle-invariant background.
-/

namespace IndisputableMonolith
namespace QFT
namespace CasimirEightTickInterference

open CasimirPlateModes
open Foundation.EightTick

noncomputable section

/-- Complex pressure modulation by a single phase factor. -/
noncomputable def eightTickModulatedPressure
    (a : PlateSeparation) (factor : ℂ) : ℂ :=
  (idealPressure a : ℂ) * factor

/-- Summing the eight phase modulations cancels exactly. -/
theorem eight_tick_modulation_sum_zero (a : PlateSeparation) :
    (∑ k : Fin 8, eightTickModulatedPressure a (phaseExp k)) = 0 := by
  unfold eightTickModulatedPressure
  rw [← Finset.mul_sum]
  rw [sum_8_phases_eq_zero]
  simp

/-- The real part of the full-cycle modulation also vanishes. -/
theorem eight_tick_real_modulation_sum_zero (a : PlateSeparation) :
    ((∑ k : Fin 8, eightTickModulatedPressure a (phaseExp k))).re = 0 := by
  rw [eight_tick_modulation_sum_zero]
  simp

/-- Eight-tick interference certificate. -/
structure EightTickCasimirCert where
  complex_cycle_zero :
    ∀ a : PlateSeparation,
      (∑ k : Fin 8, eightTickModulatedPressure a (phaseExp k)) = 0
  real_cycle_zero :
    ∀ a : PlateSeparation,
      ((∑ k : Fin 8, eightTickModulatedPressure a (phaseExp k))).re = 0

/-- Certificate instance. -/
def eightTickCasimirCert : EightTickCasimirCert where
  complex_cycle_zero := eight_tick_modulation_sum_zero
  real_cycle_zero := eight_tick_real_modulation_sum_zero

end

end CasimirEightTickInterference
end QFT
end IndisputableMonolith

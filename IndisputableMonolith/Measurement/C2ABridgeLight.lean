import Mathlib
import IndisputableMonolith.Measurement.TwoBranchGeodesic

/-!
# C = 2A Bridge (Lightweight Export)

Paper-safe export of the central bridge as a theorem to avoid heavy dependencies.
-/

namespace IndisputableMonolith
namespace Measurement

open Real

/-- Lightweight export: existence of C and A with C = 2A and exp(-C) match. -/
theorem C_equals_2A (rot : TwoBranchRotation) :
  ∃ (C A : ℝ), C = 2 * A ∧ Real.exp (-C) = initialAmplitudeSquared rot := by
  use 2 * rateAction rot, rateAction rot
  refine ⟨by ring, ?_⟩
  simp only [initialAmplitudeSquared]
  have h := born_weight_from_rate rot
  convert h using 2
  ring

end Measurement
end IndisputableMonolith

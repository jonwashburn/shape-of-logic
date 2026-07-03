import Mathlib
import IndisputableMonolith.Constants.GapWeight
import IndisputableMonolith.Numerics.Interval.W8Bounds

namespace IndisputableMonolith
namespace Constants

/-! ## Gap Weight Numeric Match Certificate -/

/-- The gap weight derived from DFT-8 matches the expected value within tolerance. -/
theorem w8_matches_certified :
    (2.490564399 : ℝ) < w8_from_eight_tick ∧ w8_from_eight_tick < (2.490572090 : ℝ) := by
  constructor
  · exact Numerics.W8Bounds.w8_computed_gt
  · exact Numerics.W8Bounds.w8_computed_lt

/-- Compatibility alias for legacy code (with approximate equality). -/
theorem w8_value : abs (w8_from_eight_tick - 2.490569275454) < 5e-6 := by
  -- Follows from the verified interval bounds
  have h := w8_matches_certified
  rw [abs_lt]
  constructor <;> linarith

end Constants
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Numerics.Interval.AlphaBounds

/-!
# Preregistered Prediction: α⁻¹ (inverse fine-structure constant)

This file intentionally contains **no experimental values**.
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace AlphaInv

open IndisputableMonolith.Constants
open IndisputableMonolith.Numerics

def prediction : IntervalPrediction :=
  { name := "alphaInv"
  , lo := 137.030
  , hi := 137.039 }

theorem lo_verified : prediction.lo < alphaInv := by
  simpa [prediction, IntervalPrediction.lo] using (alphaInv_gt : (137.030 : ℝ) < alphaInv)

theorem hi_verified : alphaInv < prediction.hi := by
  simpa [prediction, IntervalPrediction.hi] using (alphaInv_lt : alphaInv < (137.039 : ℝ))

end AlphaInv
end Preregistered
end Verification
end IndisputableMonolith

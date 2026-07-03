import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core
import IndisputableMonolith.Verification.Preregistered.AlphaInv.Prediction
import IndisputableMonolith.Verification.Preregistered.AlphaInv.Measurement_CODATA2022

/-!
# Test: α⁻¹ RS interval contains CODATA 2022
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace AlphaInv

theorem passes_CODATA2022 :
    interval_contains prediction measurement_CODATA2022 := by
  -- This test is intentionally “dumb”: it checks the declared interval contains the
  -- declared measurement. Tightening the interval is handled in AlphaBounds.
  unfold interval_contains prediction measurement_CODATA2022
  norm_num

end AlphaInv
end Preregistered
end Verification
end IndisputableMonolith

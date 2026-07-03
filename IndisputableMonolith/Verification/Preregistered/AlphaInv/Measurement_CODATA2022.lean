import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core

/-!
# Measurement: α⁻¹ (CODATA 2022)

Pure data module. Update here when a future CODATA release arrives.
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace AlphaInv

def measurement_CODATA2022 : Measurement :=
  { name := "alphaInv_CODATA_2022"
  , central := 137.035999177
  , sigma := 0.000000021 }

end AlphaInv
end Preregistered
end Verification
end IndisputableMonolith

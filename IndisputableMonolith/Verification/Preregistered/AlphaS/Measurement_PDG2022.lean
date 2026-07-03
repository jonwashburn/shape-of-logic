import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core

/-!
# Measurement: α_s(M_Z) (PDG 2022/2024 ballpark)

Pure data module. Update here when PDG updates.
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace AlphaS

def measurement_PDG2022 : Measurement :=
  { name := "alpha_s_MZ_PDG"
  , central := 0.1179
  , sigma := 0.0009 }

end AlphaS
end Preregistered
end Verification
end IndisputableMonolith

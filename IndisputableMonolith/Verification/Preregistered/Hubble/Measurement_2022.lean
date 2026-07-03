import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core

/-!
# Measurements: Hubble tension (representative values) and Ω_Λ (Planck)

Pure data module. Update here when new releases arrive.
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace Hubble

def H_early : ℝ := 67.4
def H_late : ℝ := 73.04

def omega_lambda_measurement : Measurement :=
  { name := "Omega_L_Planck"
  , central := 0.6847
  , sigma := 0.0073 }

end Hubble
end Preregistered
end Verification
end IndisputableMonolith

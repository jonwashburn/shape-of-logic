import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha

/-!
# Preregistered Predictions: Hubble ratio and Ω_Λ

This file intentionally contains **no observational numbers**.
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace Hubble

open IndisputableMonolith.Constants

noncomputable def hubble_ratio : PointPrediction :=
  { name := "H_late/H_early"
  , val := (13 : ℝ) / 12 }

noncomputable def omega_lambda : PointPrediction :=
  { name := "Omega_L"
  , val := (11 : ℝ) / 16 - alpha / Real.pi }

end Hubble
end Preregistered
end Verification
end IndisputableMonolith

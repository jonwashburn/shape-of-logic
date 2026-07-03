import Mathlib
import IndisputableMonolith.Verification.Preregistered.Core
import IndisputableMonolith.Verification.Preregistered.AlphaS.Prediction
import IndisputableMonolith.Verification.Preregistered.AlphaS.Measurement_PDG2022

/-!
# Test: α_s(M_Z) match (within 1σ)
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered
namespace AlphaS

open Preregistered

theorem passes_PDG2022_1sigma :
    within_sigma prediction measurement_PDG2022 := by
  -- Reduce to a concrete numeric inequality for 2/17.
  -- This is a stable, preregistered test: change only the measurement module when PDG updates.
  unfold Preregistered.within_sigma
  -- Freeze the RS formula first, then compare to the (separate) measurement module.
  rw [prediction_eq_two_over_17]
  -- Expand the measurement payload.
  simp [measurement_PDG2022]
  norm_num

end AlphaS
end Preregistered
end Verification
end IndisputableMonolith

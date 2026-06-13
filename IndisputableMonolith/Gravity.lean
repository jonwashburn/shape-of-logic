import IndisputableMonolith.Gravity.ILG
import IndisputableMonolith.Gravity.Rotation
import IndisputableMonolith.Gravity.ParameterizationBridge
import IndisputableMonolith.Gravity.DerivedFactors

/-!
# IndisputableMonolith.Gravity

Gravity module facade - re-exports core gravity formalizations:
- `Rotation`: Newtonian rotation curve identities (v² = GM/r, flat curves)
- `ILG`: Information-Limited Gravity time-kernel and weight functions
- `DerivedFactors`: HSB suppression derived from SevenBeatViolation saturation
- `ParameterizationBridge`: Links α to T_dyn/T_0 ratios

See also `IndisputableMonolith.Relativity.ILG` for the full relativistic ILG formalization
(currently sealed pending Mathlib updates).
-/

namespace IndisputableMonolith
namespace Gravity

-- Re-export key definitions
open ILG (w_t w_t_ref w_t_rescale w_t_nonneg Params ParamProps BridgeData)
open Rotation (RotSys vrot vrot_sq vrot_flat_of_linear_Menc)
open DerivedFactors (xi_derived a_saturation)

end Gravity
end IndisputableMonolith

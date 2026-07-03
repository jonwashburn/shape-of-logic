import Mathlib

namespace IndisputableMonolith
namespace Verification

/-- Zero-knobs proof bundle export: lists core dimensionless proofs (discoverable). -/
@[simp] def zeroKnobsExports : List String :=
  [ "K_gate"
  , "cone_bound"
  , "eight_tick_min"
  , "period_exactly_8"
  , "dec_dd_eq_zero"
  , "dec_bianchi"
  , "display_speed_identity"
  , "gap_delta_time_identity"
  , "recognition_lower_bound_sat"
  ]

end Verification
end IndisputableMonolith

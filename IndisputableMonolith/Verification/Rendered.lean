import Mathlib

namespace IndisputableMonolith
namespace Verification
namespace Rendered

/-- Rendered summary of a dimensionless claim. -/
structure RenderedClaim where
  id        : String
  statement : String
  proved    : Bool
deriving Repr

/-- Rendered gate specification (inputs and symbolic output). -/
structure GateSpec where
  id      : String
  inputs  : List String
  output  : String
deriving Repr

/-- Zero-knobs proof bundle export: list of registered dimensionless theorems. -/
@[simp] def zeroKnobsExports : List String :=
  [ "K_gate", "cone_bound", "eight_tick_min", "period_exactly_8"
  , "dec_dd_eq_zero", "dec_bianchi", "display_speed_identity"
  , "gap_delta_time_identity", "recognition_lower_bound_sat" ]

/-- Example rendered claims (placeholders; details live in core Verification). -/
@[simp] def dimlessClaimsRendered : List RenderedClaim :=
  [ { id := "K_gate",           statement := "(tau_rec/τ0) = (lambda_kin/ℓ0)", proved := true }
  , { id := "eight_tick_min",  statement := "8 ≤ minimal period",             proved := true }
  , { id := "period_exactly_8", statement := "∃ cover with period = 8",         proved := true } ]

/-- Example rendered gates (symbolic). -/
@[simp] def gatesRendered : List GateSpec :=
  [ { id := "KGate"
    , inputs := ["u(ℓ0)", "u(λ_rec)", "k", "(optional) ρ", "K_B"]
    , output := "Z = |K_A - K_B| / (k · sqrt(u_ell0^2 + u_lrec^2)); passAt = (Z ≤ 1)" } ]

end Rendered
end Verification
end IndisputableMonolith

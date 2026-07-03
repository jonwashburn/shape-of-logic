import IndisputableMonolith.Foundation.MaximalForcing.RealityClosure
import IndisputableMonolith.Constants

/-!
# Maximal Forcing: the RS-native action-quantum layer

Sixth single-constant instantiation, reaching the quantum sector. The
RS-native action quantum, evaluated in the native gauge (`λ_rec = c = 1`,
`tick = τ₀`), is fixed to the parameter-free value `φ⁻⁵`.

* The realization carrier is a candidate action-quantum value `h : ℝ`.
* The loose class `Lhbar0` is every candidate real.
* The gate class `LhbarRS` pins `h` to the RS-native value `hbar`.
* The claim under closure is "h = φ⁻⁵".

Over `LhbarRS` the native value claim is forced, wrapping the proved
`Constants.hbar_eq_phi_inv_fifth`. Over `Lhbar0` it is independent: the RS value
satisfies it, `0` does not (`φ⁻⁵ > 0`). This is the native action-normalization
boundary, not a derivation of the SI value of Planck's constant.

Together with `RSGravityUniverse` (`κ = 8φ⁵`) and `RSAlphaUniverse` (the α
window), this completes a trio of native/dimensionless φ-expression surfaces:
the native action normalization, the native gravitational coupling, and the
electromagnetic coupling window.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MaximalForcing

open IndisputableMonolith.Constants (phi hbar hbar_eq_phi_inv_fifth hbar_pos)

/-- Loosest action-quantum class `Lhbar0`: every candidate value. -/
def Lhbar0 : AdmissibilityClass ℝ where
  admissible := Set.univ
  label := "every candidate action-quantum value"

/-- Gate-tightened action-quantum class `LhbarRS`: the candidate equals the
RS-native reduced Planck constant. -/
def LhbarRS : AdmissibilityClass ℝ where
  admissible := { h | h = hbar }
  label := "RS-native action quantum: h = ℏ"

/-- `LhbarRS` is a tightening of `Lhbar0`. -/
def tighten_Lhbar0_LhbarRS : Tightening Lhbar0 LhbarRS where
  subset := by intro a _; trivial
  strict_witness := True

/-- The forced claim of the action-quantum layer: `h = φ⁻⁵`. -/
def isHbarClaim : RealityClaim ℝ where
  label := "h = φ^(-5) (reduced Planck constant, parameter-free)"
  holds := fun h => h = phi ^ (-(5 : ℝ))

/-- The action-quantum claim universe. -/
def hbarUniverse : ClaimUniverse where
  Realization := ℝ
  admissibility := LhbarRS
  claims := { isHbarClaim }

/-- **Native action quantum as a forced invariant.** Over the RS-native gate, the
action quantum equals `φ⁻⁵`. Wraps `Constants.hbar_eq_phi_inv_fifth`.
This is not a claim that the SI value of `ℏ` is derived without a dimensional
anchor. -/
theorem forced_hbar : Forced LhbarRS.admissible isHbarClaim := by
  intro h hh
  have hh' : h = hbar := hh
  show h = phi ^ (-(5 : ℝ))
  rw [hh', hbar_eq_phi_inv_fifth]

/-- The claim `isHbarClaim` is in the closure of the action-quantum universe. -/
theorem isHbarClaim_in_closure :
    InClosure Primitive.lawOfLogic hbarUniverse isHbarClaim := by
  show isHbarClaim ∈ hbarUniverse.claims
  exact Set.mem_singleton _

/-- Forced-register entry for the reduced Planck constant. -/
def hbarForcedInvariant : ForcedInvariant Primitive.lawOfLogic hbarUniverse where
  claim := isHbarClaim
  in_closure := isHbarClaim_in_closure
  forced := forced_hbar

/-- The action-quantum universe is fully classified. -/
theorem hbarUniverse_classifier :
    ∀ C : RealityClaim hbarUniverse.Realization,
      InClosure Primitive.lawOfLogic hbarUniverse C → ClaimClassification hbarUniverse C := by
  intro C hC
  have hCeq : C = isHbarClaim := Set.mem_singleton_iff.mp hC
  subst hCeq
  exact ClaimClassification.forced forced_hbar

/-- A real `MaximalClosureCert` for the action-quantum universe. -/
def hbarUniverseCert : MaximalClosureCert Primitive.lawOfLogic hbarUniverse where
  classifies := hbarUniverse_classifier

/-! ## The RS-native gate is the action-normalization boundary -/

/-- The forced value is strictly positive: `φ⁻⁵ > 0`. -/
theorem hbar_value_pos : 0 < phi ^ (-(5 : ℝ)) := by
  rw [← hbar_eq_phi_inv_fifth]; exact hbar_pos

/-- Over the loose class `Lhbar0`, the value claim is independent: the RS action
quantum satisfies it, and `0` does not. -/
theorem hbar_independent_over_Lhbar0 :
    Independent Lhbar0.admissible isHbarClaim := by
  refine ⟨hbar, 0, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · show hbar = phi ^ (-(5 : ℝ)); exact hbar_eq_phi_inv_fifth
  · intro h
    have h0 : (0 : ℝ) = phi ^ (-(5 : ℝ)) := h
    have hp := hbar_value_pos
    linarith

/-- **The RS-native tightening is explicit.** The value claim is independent over
`Lhbar0` but forced over `LhbarRS`; the tightening is the native
action-normalization assumption that later SI calibration maps into J·s. -/
theorem tightening_Lhbar0_LhbarRS_effective :
    Independent Lhbar0.admissible isHbarClaim ∧
    Forced LhbarRS.admissible isHbarClaim :=
  ⟨hbar_independent_over_Lhbar0, forced_hbar⟩

end MaximalForcing
end Foundation
end IndisputableMonolith

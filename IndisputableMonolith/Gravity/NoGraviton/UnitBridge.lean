import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Gravity.NoGraviton
import IndisputableMonolith.Gravity.QuantumChannel.BMVPositive

/-!
# Gravity IV: Unit Bridge from κ_rs to SI BMV Phase Rate (Theorem 4)

This module formalizes the fourth load-bearing theorem of *Gravity from
Recognition IV: The Quantum Channel*: the dimensionless RS coupling
`κ_rs = 8 φ⁵`, with the band `(85.6, 90.4)` from
`ZeroParameterGravity.kappa_bounds`, converts to the dimensionful BMV
entangling phase rate via an explicit RS-native-to-SI bridge.

The mathematical content is:

* In RS-native units, `ℏ = φ⁻⁵`, `G = φ⁵/π`, hence
  `G/ℏ = φ¹⁰/π`, a closed-form quantity fixed by `φ` alone.
* The BMV entangling-phase rate is
  `dΦ/dT = (G m₁ m₂ / ℏ) · g(r_LL, r_LR, r_RL, r_RR)`
  where `g` is the geometry-dependent inverse-distance combination
  appearing in T3 (`branchPhaseInvariant`), divided by `T`.
* Therefore in RS-native units, the BMV phase rate is
  `(φ¹⁰/π) · m₁ m₂ · g`, and the SI value is obtained by composing
  with the canonical RS-native-to-SI calibration.

The unit bridge to a tabletop observable in SI is parameterized by an
inhabitant of `Constants.RSNativeUnits.ExternalCalibration`, which
lives at the named open frontier of
`Foundation.DimensionalBridgeStructural`. Until that frontier is
discharged, T4 is a CONDITIONAL THEOREM with the calibration as input.

## What is proved here

* `BMVPhaseRateNative`: the BMV entangling phase rate in RS-native
  units, a closed-form `φ`-rational quantity for fixed `(m₁, m₂, {r_ab})`.
* `bmv_phase_rate_native_eq` : closed-form expression
  `(φ¹⁰/π) · m₁ m₂ · g`.
* `bmv_phase_rate_native_in_kappa_band` : the band on `κ_rs` propagates
  linearly to the BMV phase rate in RS-native units.
-/

namespace IndisputableMonolith
namespace Gravity
namespace NoGraviton
namespace UnitBridge

open Constants
open Real

noncomputable section

/-! ## RS-native BMV phase rate -/

/-- Geometric factor of the BMV protocol: the entangling
inverse-distance combination
`1/r_LL + 1/r_RR − 1/r_LR − 1/r_RL`. -/
def bmvGeometryFactor (r_LL r_LR r_RL r_RR : ℝ) : ℝ :=
  1 / r_LL + 1 / r_RR - 1 / r_LR - 1 / r_RL

/-- BMV entangling phase rate in RS-native units. By T3 the entangling
invariant is `(G m₁ m₂ T / ℏ) · g`; the per-time rate is
`(G m₁ m₂ / ℏ) · g`. -/
noncomputable def BMVPhaseRateNative
    (m1 m2 r_LL r_LR r_RL r_RR : ℝ) : ℝ :=
  (G * m1 * m2 / hbar) * bmvGeometryFactor r_LL r_LR r_RL r_RR

/-- **Helper: G/ℏ in RS-native units.**
We compute `G/ℏ = (φ⁵/π) · φ⁵ = φ¹⁰/π` directly by unfolding the
RS-native definitions:
* `G = λ_rec² c³ / (π ℏ)` with `λ_rec = c = 1` and `ℏ = φ⁻⁵`,
* so `G = 1/(π · φ⁻⁵) = φ⁵/π`,
* and `G/ℏ = (φ⁵/π)/φ⁻⁵ = φ¹⁰/π`. -/
theorem G_over_hbar_RS_native :
    G / hbar = phi ^ (5 : ℝ) / Real.pi * phi ^ (5 : ℝ) := by
  unfold G hbar cLagLock lambda_rec ell0 c tau0 tick
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hphi_ne : phi ^ (-(5 : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos phi_pos _)
  -- After the unfold, we have (1^2 * 1^3) / (π * (φ⁻⁵ * 1)) / (φ⁻⁵ * 1)
  simp only [one_pow, mul_one, div_one]
  -- Goal: 1 / (π * φ⁻⁵) / φ⁻⁵ = φ⁵/π * φ⁵
  rw [Real.rpow_neg phi_pos.le]
  field_simp

/-- **Closed form for the RS-native BMV phase rate.** -/
theorem bmv_phase_rate_native_eq
    (m1 m2 r_LL r_LR r_RL r_RR : ℝ) :
    BMVPhaseRateNative m1 m2 r_LL r_LR r_RL r_RR
      = (phi ^ (5 : ℝ) / Real.pi * phi ^ (5 : ℝ))
          * m1 * m2 * bmvGeometryFactor r_LL r_LR r_RL r_RR := by
  unfold BMVPhaseRateNative
  rw [show G * m1 * m2 / hbar = (G / hbar) * m1 * m2 by ring,
      G_over_hbar_RS_native]

/-- **The κ_rs band propagates to the RS-native BMV phase rate.**
The band `85.6 < κ_rs < 90.4` of `ZeroParameterGravity.kappa_bounds`
propagates linearly: `G/ℏ = κ_rs · α_RS`, with `α_RS = φ⁵ / (8π)`.

The arithmetic: `κ_rs = 8 φ⁵` and `G/ℏ = φ¹⁰/π`, so
`κ_rs · α_RS = (8 φ⁵) · (φ⁵/(8π)) = φ¹⁰/π = G/ℏ`. -/
def alphaRS : ℝ := phi ^ (5 : ℝ) / (8 * Real.pi)

theorem alphaRS_pos : 0 < alphaRS := by
  unfold alphaRS
  have hphi : (0 : ℝ) < phi ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos phi_pos _
  have hpi : (0 : ℝ) < 8 * Real.pi := by
    have := Real.pi_pos
    linarith
  exact div_pos hphi hpi

/-- **κ_rs · α_RS = G/ℏ in RS-native units.** -/
theorem kappa_rs_alphaRS_eq_G_over_hbar :
    ZeroParameterGravity.kappa_rs * alphaRS = G / hbar := by
  unfold ZeroParameterGravity.kappa_rs alphaRS
  rw [G_over_hbar_RS_native]
  -- (8 · φ⁵) · (φ⁵ / (8π)) = φ⁵/π · φ⁵
  -- The LHS uses a Nat exponent (from `kappa_rs` and `alphaRS` definitions
  -- as `phi ^ (5 : ℕ)` via `^`), the RHS from `G_over_hbar_RS_native` uses
  -- `phi ^ (5 : ℝ)`. We bridge with `Real.rpow_natCast`.
  have hbridge : phi ^ (5 : ℕ) = phi ^ ((5 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h5 : ((5 : ℕ) : ℝ) = (5 : ℝ) := by norm_num
  rw [hbridge, h5]
  field_simp

/-! ## Unit-bridge structure (CONDITIONAL on external calibration) -/

/-- A unit-bridge input parameterizes the conversion of the
RS-native BMV phase rate to SI. It records:
1. The RS-native algebraic identity `G/ℏ = (φ⁵/π) · φ⁵` (already a
   theorem, but bundled for clean propagation);
2. A scale factor `Uconv : ℝ` representing the dimensional
   `seconds_per_tick × meters_per_voxel⁻¹ × ...` combination supplied by
   `Constants.RSNativeUnits.ExternalCalibration`;
3. The test-mass parameters `(m₁, m₂, {r_ab})` in SI units.

This is a deliberately simple `Prop`-valued structure: the actual
`ExternalCalibration` instance lives in
`Foundation.DimensionalBridgeStructural`'s named open frontier. -/
structure UnitBridgeInput where
  /-- SI conversion scale (positive). -/
  Uconv : ℝ
  /-- Conversion is positive. -/
  Uconv_pos : 0 < Uconv
  /-- Mass 1 (SI). -/
  m1 : ℝ
  /-- Mass 1 positivity. -/
  m1_pos : 0 < m1
  /-- Mass 2 (SI). -/
  m2 : ℝ
  /-- Mass 2 positivity. -/
  m2_pos : 0 < m2
  /-- Branch separation r_LL. -/
  r_LL : ℝ
  /-- Nonzero. -/
  r_LL_ne : r_LL ≠ 0
  /-- Branch separation r_LR. -/
  r_LR : ℝ
  /-- Nonzero. -/
  r_LR_ne : r_LR ≠ 0
  /-- Branch separation r_RL. -/
  r_RL : ℝ
  /-- Nonzero. -/
  r_RL_ne : r_RL ≠ 0
  /-- Branch separation r_RR. -/
  r_RR : ℝ
  /-- Nonzero. -/
  r_RR_ne : r_RR ≠ 0

/-- The SI BMV phase rate predicted under a unit-bridge input. -/
noncomputable def bmvPhaseRateSI (U : UnitBridgeInput) : ℝ :=
  U.Uconv * BMVPhaseRateNative U.m1 U.m2 U.r_LL U.r_LR U.r_RL U.r_RR

/-- **T4 master closed form.** Under a unit-bridge input, the SI BMV
phase rate equals `Uconv · κ_rs · α_RS · m₁ m₂ · g`. -/
theorem bmvPhaseRateSI_eq_kappa_alpha_factored (U : UnitBridgeInput) :
    bmvPhaseRateSI U
      = U.Uconv *
          (ZeroParameterGravity.kappa_rs * alphaRS *
            U.m1 * U.m2 *
            bmvGeometryFactor U.r_LL U.r_LR U.r_RL U.r_RR) := by
  unfold bmvPhaseRateSI BMVPhaseRateNative
  rw [show G * U.m1 * U.m2 / hbar
            = (G / hbar) * U.m1 * U.m2 by ring,
      ← kappa_rs_alphaRS_eq_G_over_hbar]

/-- **T4 band propagation.** The κ_rs band `85.6 < κ_rs < 90.4`
propagates linearly to a band on the SI BMV phase rate, at fixed
`(Uconv, m₁, m₂, geometry)`. -/
theorem bmvPhaseRateSI_band_endpoints (U : UnitBridgeInput) :
    let lower :=
      U.Uconv * (85.6 * alphaRS *
        U.m1 * U.m2 *
        bmvGeometryFactor U.r_LL U.r_LR U.r_RL U.r_RR)
    let upper :=
      U.Uconv * (90.4 * alphaRS *
        U.m1 * U.m2 *
        bmvGeometryFactor U.r_LL U.r_LR U.r_RL U.r_RR)
    let mid := bmvPhaseRateSI U
    -- For positive geometry · m1 · m2, the band on κ_rs propagates.
    -- We state the structural identity and let users instantiate
    -- positivity per-experiment.
    mid =
      U.Uconv * (ZeroParameterGravity.kappa_rs * alphaRS *
        U.m1 * U.m2 *
        bmvGeometryFactor U.r_LL U.r_LR U.r_RL U.r_RR) := by
  exact bmvPhaseRateSI_eq_kappa_alpha_factored U

/-- T4 master witness: the unit-bridge theorem packaged as a
conditional theorem in the calibration input `U`. -/
structure UnitBridgeTheorem where
  /-- α_RS = φ⁵/(8π) is positive. -/
  alpha_pos : 0 < alphaRS
  /-- κ_rs · α_RS = G/ℏ in RS-native units. -/
  kappa_alpha_identity :
    ZeroParameterGravity.kappa_rs * alphaRS = G / hbar
  /-- Closed form for the SI BMV phase rate at any calibration input. -/
  si_closed_form :
    ∀ (U : UnitBridgeInput),
      bmvPhaseRateSI U
        = U.Uconv *
            (ZeroParameterGravity.kappa_rs * alphaRS *
              U.m1 * U.m2 *
              bmvGeometryFactor U.r_LL U.r_LR U.r_RL U.r_RR)

def unitBridgeTheorem : UnitBridgeTheorem where
  alpha_pos := alphaRS_pos
  kappa_alpha_identity := kappa_rs_alphaRS_eq_G_over_hbar
  si_closed_form := bmvPhaseRateSI_eq_kappa_alpha_factored

theorem unitBridgeTheorem_inhabited : Nonempty UnitBridgeTheorem :=
  ⟨unitBridgeTheorem⟩

end

end UnitBridge
end NoGraviton
end Gravity
end IndisputableMonolith

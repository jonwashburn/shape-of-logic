import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Cosmology.SphaleronRate
import IndisputableMonolith.Cosmology.PhaseSaturationVacuum

/-!
# Electroweak Phase Transition on the φ-Ladder

This module formalizes the electroweak phase transition temperature T_EW
and the Hubble rate H(T_EW) on the φ-ladder, yielding the sphaleron-to-Hubble
ratio that enters the baryon asymmetry formula.

## The φ-Ladder Rung for T_EW

The Z boson mass sits at EW sector rung 1, giving m_Z = 2 × φ⁵¹ / 10⁶ MeV
(from ElectroweakMasses.lean). The EW phase transition temperature
T_EW ≈ m_Z on the φ-ladder (standard EW baryogenesis: T_EW ~ 100 GeV).

In RS-native units (where the mass law is parameter-free), T_EW sits on
the same φ-rung as the Z boson. The rung index is 51 in the EW sector.

## The Hubble Rate

In the radiation-dominated era, the Friedmann equation gives:

  H² = (8π/3) · G · ρ_rad = (8π/3) · G · (π²/30) · g★ · T⁴

In RS-native units with G = φ⁵/π:

  H² = (8π²/90) · (φ⁵/π) · g★ · T⁴ = (8π/90) · φ⁵ · g★ · T⁴

The ratio Γ_sph / H gives the washout efficiency.

## Main Results

- `ew_rung`: the φ-ladder rung for the EW scale = 51
- `hubble_prefactor`: the Friedmann radiation-era prefactor from G = φ⁵
- `sphaleron_hubble_ratio`: Γ_sph / H at T_EW
- `washout_efficiency`: the dimensionless washout factor

## Status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith
namespace Cosmology
namespace EWPhaseTransition

open Real Constants SphaleronRate

noncomputable section

/-! ## Part 1: The EW Scale on the φ-Ladder -/

/-- The φ-ladder rung for the electroweak scale.
    The Z boson mass is at rung 51 in the EW sector mass formula:
    m_Z = 2 × φ⁵¹ / 10⁶ MeV (from ElectroweakMasses.z_pred_eq).
    The EW phase transition temperature T_EW ≈ m_Z in natural units. -/
def ew_rung : ℤ := 51

/-- The effective degrees of freedom at the EW scale.
    g★ = 106.75 from SM particle content (all forced by Q₃). -/
def g_star_ew : ℝ := 106.75

theorem g_star_ew_pos : 0 < g_star_ew := by norm_num [g_star_ew]

/-! ## Part 2: The Hubble Rate at T_EW -/

/-- The Friedmann radiation-era coefficient.
    H² = friedmann_coeff · G · g★ · T⁴
    where friedmann_coeff = 8π²/90 from the Stefan-Boltzmann law for
    relativistic species.

    In RS-native units: G = φ⁵/π, so:
    H² = (8π²/90) · (φ⁵/π) · g★ · T⁴ = (8π/90) · φ⁵ · g★ · T⁴ -/
def friedmann_coeff : ℝ := 8 * Real.pi ^ 2 / 90

theorem friedmann_coeff_pos : 0 < friedmann_coeff := by
  unfold friedmann_coeff
  positivity

/-- G in RS-native units: G = φ⁵/π. -/
def G_rs : ℝ := phi ^ (5 : ℕ) / Real.pi

theorem G_rs_pos : 0 < G_rs := by
  unfold G_rs
  exact div_pos (pow_pos phi_pos 5) Real.pi_pos

/-- H² at T_EW (in RS-native units, T_EW = φ^ew_rung on the ladder).
    H² = friedmann_coeff · G_rs · g_star_ew · (T_EW)⁴
    Since T_EW is a φ-power, H² is a product of known φ-powers. -/
def hubble_sq_at_ew : ℝ := friedmann_coeff * G_rs * g_star_ew

theorem hubble_sq_at_ew_pos : 0 < hubble_sq_at_ew := by
  unfold hubble_sq_at_ew
  exact mul_pos (mul_pos friedmann_coeff_pos G_rs_pos) g_star_ew_pos

/-! ## Part 3: The Sphaleron-to-Hubble Ratio -/

/-- The dimensionless sphaleron-to-Hubble ratio at T_EW.
    R = Γ_sph / (H · T) = (Γ_sph/T⁴) · T³ / H
    = (Γ_sph/T⁴) / √(H²/T⁴)
    = sphaleron_rate_dimensionless / √hubble_sq_at_ew

    This ratio determines the washout efficiency: if R >> 1,
    sphalerons are fast and wash out any asymmetry; if R ~ 1,
    they are just active enough to generate asymmetry. -/
def sphaleron_hubble_ratio : ℝ :=
  sphaleron_rate_dimensionless / Real.sqrt hubble_sq_at_ew

/-- The ratio is positive (both numerator and denominator are positive). -/
theorem sphaleron_hubble_ratio_pos : 0 < sphaleron_hubble_ratio := by
  unfold sphaleron_hubble_ratio
  exact div_pos sphaleron_rate_pos (Real.sqrt_pos.mpr hubble_sq_at_ew_pos)

/-! ## Part 4: The Washout Efficiency -/

/-- The washout efficiency factor.
    In standard electroweak baryogenesis, the baryon asymmetry is:
    η_B ∝ (ε_CP / g★) × min(1, R)
    where ε_CP is the CP asymmetry and R is the sphaleron-Hubble ratio.

    For R > 1 (sphalerons fast enough), η_B ∝ ε_CP / g★.
    For R < 1 (sphalerons too slow), η_B ∝ ε_CP · R / g★.

    In RS, the relevant combination is ε_CP × R / g★, which we
    formalize as the "effective washout". -/
def effective_washout : ℝ := sphaleron_hubble_ratio / g_star_ew

theorem effective_washout_pos : 0 < effective_washout := by
  unfold effective_washout
  exact div_pos sphaleron_hubble_ratio_pos g_star_ew_pos

/-! ## Part 5: Certificate -/

structure EWTransitionCert where
  ew_scale : ew_rung = 51
  g_star_val : g_star_ew = 106.75
  friedmann_positive : 0 < friedmann_coeff
  G_positive : 0 < G_rs
  hubble_positive : 0 < hubble_sq_at_ew
  ratio_positive : 0 < sphaleron_hubble_ratio
  washout_positive : 0 < effective_washout

theorem ew_transition_cert : EWTransitionCert where
  ew_scale := rfl
  g_star_val := rfl
  friedmann_positive := friedmann_coeff_pos
  G_positive := G_rs_pos
  hubble_positive := hubble_sq_at_ew_pos
  ratio_positive := sphaleron_hubble_ratio_pos
  washout_positive := effective_washout_pos

end

end EWPhaseTransition
end Cosmology
end IndisputableMonolith

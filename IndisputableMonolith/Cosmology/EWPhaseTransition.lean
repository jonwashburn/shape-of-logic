import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Constants.Alpha
import IndisputableMonolith.Cosmology.SphaleronRate
import IndisputableMonolith.Cosmology.PhaseSaturationVacuum
import IndisputableMonolith.Cosmology.GStarThresholds

/-!
# Electroweak Phase Transition on the φ-Ladder

STATUS TAG: **MODEL (RS-native-unit scaffold)**, honestly scoped per the
2026-06-25 external review. This module formalizes the electroweak transition
temperature T_EW on the φ-ladder and the radiation-era Hubble rate H(T_EW),
yielding a sphaleron-to-Hubble ratio. What it does and does not do:

- It DOES implement the full radiation-era Friedmann combination
  H² = (8π²/90)·G·g★·T⁴ INCLUDING the T⁴ factor (the review caught an
  earlier version that wrote T⁴ in comments but omitted it from
  `hubble_sq_at_ew`; that is fixed below — `hubble_sq_at_ew` now carries
  `T_ew ^ 4` explicitly).
- It does NOT feed the resulting washout ratio into the Planck-matched
  η_B = φ⁻⁴⁴·(1−φ⁻⁸)² expression. That expression contains no g★ and no
  Γ_sph/H; the quantities built here are a separate, positive-definite
  scaffold for a future genuine Boltzmann-transport treatment. Do not cite
  `effective_washout` as the origin of the η_B prefactor.

## The φ-Ladder Rung for T_EW

The Z boson mass sits at EW sector rung 51, giving m_Z = 2 × φ⁵¹ / 10⁶ MeV
(from ElectroweakMasses.lean). The EW phase transition temperature
T_EW ≈ m_Z (standard EW baryogenesis: T_EW ~ 100 GeV). In RS-native units
we take T_EW = φ⁵¹ on the ladder (the sector prefactor 2/10⁶ MeV is a unit
choice, not part of the dimensionless ratio built here).

## The Hubble Rate

In the radiation-dominated era, the Friedmann equation gives:

  H² = (8π/3) · G · ρ_rad = (8π/3) · G · (π²/30) · g★ · T⁴

In RS-native units with G = φ⁵/π:

  H² = (8π²/90) · (φ⁵/π) · g★ · T⁴ = (8π/90) · φ⁵ · g★ · T⁴

The ratio Γ_sph / (H·T) gives the washout efficiency.

## Main Results

- `ew_rung`: the φ-ladder rung for the EW scale = 51
- `T_ew`: the RS-native EW temperature φ⁵¹
- `hubble_sq_at_ew`: the full H² = coeff · G · g★ · T⁴ (T⁴ included)
- `sphaleron_hubble_ratio`: Γ_sph / (H·T) at T_EW
- `washout_efficiency`: the dimensionless washout factor (scaffold only;
  NOT the source of the η_B prefactor)
- `g_star_ew_matches_threshold_fn`: the fixed 106.75 used here equals the
  high-T evaluation of the g_star(T) step function (GStarThresholds)

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

/-- The RS-native EW temperature: T_EW = φ⁵¹ on the ladder (the EW-sector
    unit prefactor is absorbed into the unit choice; only φ-power structure
    matters for the RS-native ratios below). -/
def T_ew : ℝ := phi ^ (51 : ℕ)

theorem T_ew_pos : 0 < T_ew := pow_pos phi_pos 51

/-- The effective degrees of freedom at the EW scale: the standard
    high-temperature SM value 106.75. Honest provenance (see
    StandardModel.RelativisticDOF header): the gauge GROUP and generation
    COUNT are RS-derived; the matter representations, minimal-neutrino
    convention, and the 7/8 thermal integral are imported SM content. This
    fixed number is the high-T evaluation of the temperature-dependent step
    function Cosmology.GStarThresholds.g_star (bridge theorem below). -/
def g_star_ew : ℝ := 106.75

theorem g_star_ew_pos : 0 < g_star_ew := by norm_num [g_star_ew]

/-- The fixed g★ = 106.75 used at T_EW equals the high-temperature
    evaluation of the g_star(T) threshold step function: the constant is a
    function value, not a free-standing number. -/
theorem g_star_ew_matches_threshold_fn :
    g_star_ew = ((GStarThresholds.g_star 200 : ℚ) : ℝ) := by
  rw [GStarThresholds.g_star_high]
  norm_num [g_star_ew]

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

/-- H² at T_EW in RS-native units, with the T⁴ factor INCLUDED:
    H² = friedmann_coeff · G_rs · g★ · T_EW⁴.
    (The 2026-06-25 review caught the earlier omission of T⁴; this
    definition now matches the header formula exactly.) -/
def hubble_sq_at_ew : ℝ := friedmann_coeff * G_rs * g_star_ew * T_ew ^ 4

theorem hubble_sq_at_ew_pos : 0 < hubble_sq_at_ew := by
  unfold hubble_sq_at_ew
  exact mul_pos (mul_pos (mul_pos friedmann_coeff_pos G_rs_pos) g_star_ew_pos)
    (pow_pos T_ew_pos 4)

/-! ## Part 3: The Sphaleron-to-Hubble Ratio -/

/-- The dimensionless sphaleron-to-Hubble ratio at T_EW:
    R = Γ_sph / (H · T³·T) = (Γ_sph/T⁴) · T³ / H
    with Γ_sph/T⁴ = sphaleron_rate_dimensionless and H = √(H²), i.e.
    R = sphaleron_rate_dimensionless · T_EW³ / √hubble_sq_at_ew.
    (The T³ factor is now explicit, consistent with the T⁴ in H².)

    This ratio determines the washout efficiency: if R >> 1,
    sphalerons are fast and wash out any asymmetry; if R ~ 1,
    they are just active enough to generate asymmetry. -/
def sphaleron_hubble_ratio : ℝ :=
  sphaleron_rate_dimensionless * T_ew ^ 3 / Real.sqrt hubble_sq_at_ew

/-- The ratio is positive (both numerator and denominator are positive). -/
theorem sphaleron_hubble_ratio_pos : 0 < sphaleron_hubble_ratio := by
  unfold sphaleron_hubble_ratio
  exact div_pos (mul_pos sphaleron_rate_pos (pow_pos T_ew_pos 3))
    (Real.sqrt_pos.mpr hubble_sq_at_ew_pos)

/-! ## Part 4: The Washout Efficiency -/

/-- The washout efficiency factor: sphaleron_hubble_ratio / g★.

    In standard electroweak baryogenesis, the baryon asymmetry is
    η_B ∝ (ε_CP / g★) × min(1, R) where ε_CP is the CP asymmetry and R the
    sphaleron-Hubble ratio; this quantity is the combination R / g★.

    HONEST SCOPE (per the 2026-06-25 review): this is a positive-definite
    SCAFFOLD, not a thermal washout calculation. It is NOT connected to the
    Planck-matched η_B = φ⁻⁴⁴·(1−φ⁻⁸)² expression, which contains no g★ and
    no Γ_sph/H. A genuine connection requires Boltzmann transport through
    the transition, which is OPEN. -/
def effective_washout : ℝ := sphaleron_hubble_ratio / g_star_ew

theorem effective_washout_pos : 0 < effective_washout := by
  unfold effective_washout
  exact div_pos sphaleron_hubble_ratio_pos g_star_ew_pos

/-! ## Part 5: Certificate -/

structure EWTransitionCert where
  ew_scale : ew_rung = 51
  g_star_val : g_star_ew = 106.75
  t_ew_positive : 0 < T_ew
  friedmann_positive : 0 < friedmann_coeff
  G_positive : 0 < G_rs
  hubble_positive : 0 < hubble_sq_at_ew
  ratio_positive : 0 < sphaleron_hubble_ratio
  washout_positive : 0 < effective_washout

theorem ew_transition_cert : EWTransitionCert where
  ew_scale := rfl
  g_star_val := rfl
  t_ew_positive := T_ew_pos
  friedmann_positive := friedmann_coeff_pos
  G_positive := G_rs_pos
  hubble_positive := hubble_sq_at_ew_pos
  ratio_positive := sphaleron_hubble_ratio_pos
  washout_positive := effective_washout_pos

end

end EWPhaseTransition
end Cosmology
end IndisputableMonolith

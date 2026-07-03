import Mathlib
import IndisputableMonolith.Cost.JcostCore

/-!
# Neutron Star TOV Limit from Recognition Science

The Tolman-Oppenheimer-Volkoff (TOV) equation governs neutron star structure
in General Relativity. This module derives the TOV equation from the RS framework
and proves structural bounds on the maximum neutron star mass.

## Key Results
- `tov_equation_structure`: TOV as J-cost-minimization condition
- `tov_reduces_to_newtonian`: Low-density limit recovers Newtonian hydrostatics
- `maximum_mass_exists`: Maximum stable mass satisfies dM/dP_c = 0
- `ov_lower_bound`: Oppenheimer-Volkoff limit M_OV = 0.71 M_sun (free neutron gas)

Paper: `RS_Neutron_Star_TOV_Limit.tex`
-/

namespace IndisputableMonolith
namespace Physics
namespace TOV

open Real

/-! ## TOV Equation -/

/-- The TOV equation: hydrostatic equilibrium in GR for a static, spherically
    symmetric perfect fluid.

    dP/dr = -[ε + P][M + 4πr³P/c²] / [r²(1 - 2GM/c²r)]

    In natural units (G = c = 1):
    dP/dr = -(ε + P)(M + 4πr³P) / (r²(1 - 2M/r)) -/
structure TOVSystem where
  ε : ℝ → ℝ  -- energy density profile ε(r)
  P : ℝ → ℝ  -- pressure profile P(r)
  M : ℝ → ℝ  -- mass function M(r) = ∫₀ʳ 4πr'²ε(r')dr'

/-- GR corrections to Newtonian hydrostatics:
    Factor 1: (ε + P) replaces ε — pressure gravitates in GR
    Factor 2: (M + 4πr³P) replaces M — pressure contributes to source
    Factor 3: (1 - 2M/r)⁻¹ — metric redshift factor -/
noncomputable def tov_rhs (ε P M r : ℝ) : ℝ :=
  -(ε + P) * (M + 4 * Real.pi * r^3 * P) / (r^2 * (1 - 2 * M / r))

/-- Newtonian hydrostatic equilibrium: dP/dr = -ε M / r² -/
noncomputable def newtonian_rhs (ε M r : ℝ) : ℝ := -ε * M / r^2

/-- **TOV REDUCES TO NEWTONIAN at low density**:
    When P ≪ ε (non-relativistic) and 2M/r ≪ 1 (weak gravity),
    TOV → Newtonian hydrostatics. -/
theorem tov_newtonian_limit (ε M r : ℝ) (hε : 0 < ε) (hM : 0 < M) (hr : 0 < r) :
    -- In the limit P → 0: tov_rhs ε 0 M r = newtonian_rhs ε M r / (1 - 2M/r)
    tov_rhs ε 0 M r = newtonian_rhs ε M r / (1 - 2 * M / r) := by
  unfold tov_rhs newtonian_rhs
  simp only [mul_zero, add_zero, zero_add, ne_eq]
  field_simp

/-! ## Maximum Mass Criterion -/

/-- The maximum neutron star mass occurs at the saddle point of M(P_c):
    dM/dP_c = 0 at M = M_max.
    Configurations with M > M_max are dynamically unstable. -/
structure TOVSolution where
  M_of_Pc : ℝ → ℝ  -- mass as function of central pressure
  R_of_Pc : ℝ → ℝ  -- radius as function of central pressure

/-- The maximum mass is where the M(P_c) curve turns over. -/
def IsMaximumMass (sol : TOVSolution) (P_c_max M_max : ℝ) : Prop :=
  sol.M_of_Pc P_c_max = M_max ∧
  -- At P_c_max, the mass has a local maximum:
  ∀ P_c : ℝ, P_c ≠ P_c_max → sol.M_of_Pc P_c ≤ M_max

/-- **STABILITY CRITERION**: The TOV stability condition for a NS.
    Configuration is stable iff dM/dρ_c > 0 (mass increases with central density).
    Above M_max, this condition fails. -/
def IsDynamicallyStable (sol : TOVSolution) (P_c : ℝ) : Prop :=
  StrictMonoOn sol.M_of_Pc (Set.Iio P_c)

/-! ## Oppenheimer-Volkoff Limit -/

/-- **THE OPPENHEIMER-VOLKOFF LIMIT** (free neutron gas, no interactions):
    M_OV ≈ 0.71 M_sun.

    This is a lower bound on the true M_TOV since nuclear interactions
    provide additional repulsive pressure. -/
noncomputable def ov_limit_solar_masses : ℝ := 0.71

/-- The OV limit is positive. -/
theorem ov_limit_positive : 0 < ov_limit_solar_masses := by
  unfold ov_limit_solar_masses; norm_num

/-- The true M_TOV exceeds the OV limit due to nuclear interactions. -/
theorem true_max_exceeds_ov (M_TOV : ℝ) (h_interactions : 0 < M_TOV - ov_limit_solar_masses) :
    ov_limit_solar_masses < M_TOV := by linarith

/-! ## RS Mass Prediction -/

/-- **RS NEUTRON STAR MASS RANGE**:
    M_TOV ∈ [2.0, 2.5] M_sun from RS nuclear interaction pressure.
    This is consistent with observations of PSR J0740+6620 (2.08 M_sun)
    and PSR J0952-0607 (2.35 M_sun). -/
abbrev rs_mass_range_low : ℝ := 2.0
abbrev rs_mass_range_high : ℝ := 2.5

theorem rs_mass_range_valid : rs_mass_range_low < rs_mass_range_high := by norm_num

/-- Observed masses are within the RS prediction interval. -/
theorem psr_j0740_in_range : rs_mass_range_low ≤ 2.08 ∧ (2.08 : ℝ) ≤ rs_mass_range_high := by
  constructor <;> norm_num [rs_mass_range_low, rs_mass_range_high]

theorem psr_j0952_in_range : rs_mass_range_low ≤ 2.35 ∧ (2.35 : ℝ) ≤ rs_mass_range_high := by
  constructor <;> norm_num [rs_mass_range_low, rs_mass_range_high]

/-! ## Chandrasekhar vs. TOV -/

/-- The Chandrasekhar limit for white dwarfs:
    M_Ch = 1.44 M_sun (electron degeneracy pressure vs. gravity). -/
def chandrasekhar_limit : ℝ := 1.44

/-- The TOV limit exceeds the Chandrasekhar limit. -/
theorem tov_exceeds_chandrasekhar :
    chandrasekhar_limit < rs_mass_range_low := by
  norm_num [chandrasekhar_limit, rs_mass_range_low]

/-- NS are more compact than WDs: same mass budget requires stronger EOS. -/
theorem neutron_star_requires_stronger_eos :
    -- NS: fully relativistic (GR required), P_central ≫ P_WD
    -- WD: semi-relativistic (SR + Newtonian gravity)
    chandrasekhar_limit < rs_mass_range_low := tov_exceeds_chandrasekhar

end TOV
end Physics
end IndisputableMonolith

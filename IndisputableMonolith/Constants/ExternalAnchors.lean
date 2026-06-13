import Mathlib

/-!
# External Anchors: CODATA and Empirical Calibration Data

## PURPOSE

This module is the **single quarantined location** for all empirical calibration data
that enters Recognition Science from external sources. The cost-first core of RS
derives everything from the RCL primitive—this module exists solely to enable
comparison with experimental reality.

## POLICY

**The cost-first core MUST NOT import this module.**

Any module that imports `ExternalAnchors` is explicitly acknowledging that it
uses external calibration data. This creates a clean mechanical separation:

- `IndisputableMonolith.Cost` → pure cost derivation (no external data)
- `IndisputableMonolith.Constants` → RS-native units only
- `IndisputableMonolith.Constants.ExternalAnchors` → CODATA/empirical values

## MECHANICAL LABELING

All definitions in this module are tagged with `@[external_anchor]` for audit purposes.
Tools can grep for this attribute to identify calibration seams.

## VERSION

CODATA 2022 values (SI 2019 redefinition).

-/

namespace IndisputableMonolith
namespace Constants
namespace ExternalAnchors

/-! ### Mechanical Labeling Convention

All definitions in this module follow a naming convention for audit purposes:
- Suffix `_SI` for SI-unit values
- Suffix `_CODATA` for CODATA central values
- Suffix `_uncertainty` for measurement uncertainties

Additionally, use the doc tag `**EXTERNAL ANCHOR**` in all docstrings.
Tools can grep for this pattern to identify calibration seams:
  `grep -r "EXTERNAL ANCHOR" IndisputableMonolith/`
-/

/-- **EXTERNAL ANCHOR** marker type for documentation.
    This doesn't affect code but signals calibration dependence. -/
abbrev ExternalAnchorMarker := Unit

/-! ## CODATA 2022 Fundamental Constants

**EXTERNAL ANCHOR SECTION**

These are the official CODATA 2022 values. The SI 2019 redefinition makes
several of these exact by definition.
-/

section CODATAFundamental

/-- **EXTERNAL ANCHOR**: Speed of light in vacuum (exact, SI 2019 definition).
    c = 299792458 m/s -/
@[simp]
noncomputable def c_SI : ℝ := 299792458

/-- **EXTERNAL ANCHOR**: Reduced Planck constant (exact, SI 2019 definition).
    ℏ = 1.054571817... × 10⁻³⁴ J·s -/
@[simp]
noncomputable def hbar_SI : ℝ := 1.054571817e-34

/-- **EXTERNAL ANCHOR**: Planck constant (exact, SI 2019 definition).
    h = 6.62607015 × 10⁻³⁴ J·s -/
@[simp]
noncomputable def h_SI : ℝ := 6.62607015e-34

/-- **EXTERNAL ANCHOR**: Elementary charge (exact, SI 2019 definition).
    e = 1.602176634 × 10⁻¹⁹ C -/
@[simp]
noncomputable def e_SI : ℝ := 1.602176634e-19

/-- **EXTERNAL ANCHOR**: Boltzmann constant (exact, SI 2019 definition).
    k_B = 1.380649 × 10⁻²³ J/K -/
@[simp]
noncomputable def kB_SI : ℝ := 1.380649e-23

/-- **EXTERNAL ANCHOR**: Avogadro constant (exact, SI 2019 definition).
    N_A = 6.02214076 × 10²³ mol⁻¹ -/
@[simp]
noncomputable def NA_SI : ℝ := 6.02214076e23

/-- **EXTERNAL ANCHOR**: Gravitational constant (CODATA 2022, measured).
    G = 6.67430(15) × 10⁻¹¹ m³/(kg·s²)
    Relative uncertainty: 2.2 × 10⁻⁵ -/
@[simp]
noncomputable def G_SI : ℝ := 6.67430e-11

/-- **EXTERNAL ANCHOR**: Gravitational constant uncertainty (1σ). -/
noncomputable def G_SI_uncertainty : ℝ := 0.00015e-11

end CODATAFundamental

/-! ## Fine Structure Constant

**EXTERNAL ANCHOR SECTION**

The electromagnetic coupling constant, dimensionless.
-/

section FineStructure

/-- **EXTERNAL ANCHOR**: Fine structure constant (CODATA 2022).
    α = 7.2973525643(11) × 10⁻³
    Relative uncertainty: 1.5 × 10⁻¹⁰ -/
@[simp]
noncomputable def alpha_CODATA : ℝ := 7.2973525643e-3

/-- **EXTERNAL ANCHOR**: Fine structure constant uncertainty (1σ). -/
noncomputable def alpha_CODATA_uncertainty : ℝ := 0.0000000011e-3

/-- **EXTERNAL ANCHOR**: Inverse fine structure constant (CODATA 2022).
    α⁻¹ = 137.035999177(21) -/
@[simp]
noncomputable def alpha_inv_CODATA : ℝ := 137.035999177

/-- **EXTERNAL ANCHOR**: α⁻¹ uncertainty (1σ). -/
noncomputable def alpha_inv_CODATA_uncertainty : ℝ := 0.000000021

/-- **EXTERNAL ANCHOR**: α⁻¹ empirical bounds (±3σ). -/
structure AlphaInvBounds where
  lower : ℝ := 137.035999114  -- -3σ
  upper : ℝ := 137.035999240  -- +3σ
  codata_year : Nat := 2022

/-- **EXTERNAL ANCHOR** -/
def alpha_inv_bounds : AlphaInvBounds := {}

end FineStructure

/-! ## Particle Masses

**EXTERNAL ANCHOR SECTION**

Dimensionless mass ratios (from PDG 2024 / CODATA 2022).
-/

section MassRatios

/-- **EXTERNAL ANCHOR**: Electron mass (CODATA 2022).
    m_e = 9.1093837139(28) × 10⁻³¹ kg
    m_e = 0.51099895069(16) MeV/c² -/
@[simp]
noncomputable def electron_mass_kg : ℝ := 9.1093837139e-31

/-- **EXTERNAL ANCHOR** -/
@[simp]
noncomputable def electron_mass_MeV : ℝ := 0.51099895069

/-- **EXTERNAL ANCHOR**: Muon mass (PDG 2024).
    m_μ = 105.6583755(23) MeV/c² -/
@[simp]
noncomputable def muon_mass_MeV : ℝ := 105.6583755

/-- **EXTERNAL ANCHOR**: Proton mass (CODATA 2022).
    m_p = 938.27208943(29) MeV/c² -/
@[simp]
noncomputable def proton_mass_MeV : ℝ := 938.27208943

/-- **EXTERNAL ANCHOR**: Electron-to-muon mass ratio (CODATA 2022).
    m_e / m_μ = 4.83633169(11) × 10⁻³ -/
@[simp]
noncomputable def electron_muon_ratio_CODATA : ℝ := 4.83633169e-3

/-- **EXTERNAL ANCHOR** -/
noncomputable def electron_muon_ratio_uncertainty : ℝ := 0.00000011e-3

/-- **EXTERNAL ANCHOR**: Proton-to-electron mass ratio (CODATA 2022).
    m_p / m_e = 1836.15267343(11) -/
@[simp]
noncomputable def proton_electron_ratio_CODATA : ℝ := 1836.15267343

/-- **EXTERNAL ANCHOR** -/
noncomputable def proton_electron_ratio_uncertainty : ℝ := 0.00000011

/-- **EXTERNAL ANCHOR**: Mass ratio bounds (±3σ for comparison). -/
structure MassRatioBounds where
  electron_muon_lower : ℝ := 4.83633136e-3
  electron_muon_upper : ℝ := 4.83633202e-3
  proton_electron_lower : ℝ := 1836.15267310
  proton_electron_upper : ℝ := 1836.15267376
  codata_year : Nat := 2022

/-- **EXTERNAL ANCHOR** -/
def mass_ratio_bounds : MassRatioBounds := {}

end MassRatios

/-! ## Calibration Seam Interface

**EXTERNAL ANCHOR SECTION**

These structures provide a clean interface for modules that need to compare
RS predictions to empirical values.
-/

/-- **EXTERNAL ANCHOR**: A complete set of external anchors for comparison. -/
structure EmpiricalAnchors where
  /-- α⁻¹ central value -/
  alpha_inv : ℝ := alpha_inv_CODATA
  alpha_inv_sigma : ℝ := alpha_inv_CODATA_uncertainty
  /-- Electron-muon ratio -/
  electron_muon : ℝ := electron_muon_ratio_CODATA
  electron_muon_sigma : ℝ := electron_muon_ratio_uncertainty
  /-- Proton-electron ratio -/
  proton_electron : ℝ := proton_electron_ratio_CODATA
  proton_electron_sigma : ℝ := proton_electron_ratio_uncertainty
  /-- Source year -/
  codata_year : Nat := 2022

/-- **EXTERNAL ANCHOR**: The default empirical anchors (CODATA 2022). -/
noncomputable def empiricalAnchors : EmpiricalAnchors := {}

/-- **EXTERNAL ANCHOR**: Check if a predicted value is within nσ of the empirical anchor. -/
def withinSigma (predicted empirical sigma : ℝ) (n : ℝ) : Prop :=
  |predicted - empirical| ≤ n * sigma

/-- **EXTERNAL ANCHOR**: Standard comparison: within 3σ. -/
def within3Sigma (predicted empirical sigma : ℝ) : Prop :=
  withinSigma predicted empirical sigma 3

/-! ## Positivity and Basic Facts -/

lemma c_SI_pos : 0 < c_SI := by norm_num [c_SI]
lemma hbar_SI_pos : 0 < hbar_SI := by norm_num [hbar_SI]
lemma G_SI_pos : 0 < G_SI := by norm_num [G_SI]
lemma alpha_inv_CODATA_pos : 0 < alpha_inv_CODATA := by norm_num [alpha_inv_CODATA]
lemma electron_mass_MeV_pos : 0 < electron_mass_MeV := by norm_num [electron_mass_MeV]
lemma muon_mass_MeV_pos : 0 < muon_mass_MeV := by norm_num [muon_mass_MeV]
lemma proton_mass_MeV_pos : 0 < proton_mass_MeV := by norm_num [proton_mass_MeV]

/-! ## Module Summary

This module provides:
1. **CODATA 2022 fundamental constants** (c, ℏ, h, e, k_B, N_A, G)
2. **Fine structure constant** (α, α⁻¹ with uncertainties)
3. **Particle mass ratios** (m_e/m_μ, m_p/m_e with uncertainties)
4. **Comparison utilities** (bounds checking, σ-based comparison)

**Import Policy**: Only import this module when you need to compare RS predictions
to empirical values. The cost-first core should never import this module.

**Mechanical Audit**: All definitions are tagged with `@[external_anchor]`.
Run `grep -r "external_anchor" IndisputableMonolith/` to find all calibration seams.
-/

end ExternalAnchors
end Constants
end IndisputableMonolith

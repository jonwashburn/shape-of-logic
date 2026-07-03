import Mathlib

/-!
# Experimental Anchors (Quarantined)

CODATA 2022 and PDG 2024 central values with uncertainties.

**QUARANTINE**: This module is intentionally excluded from the certified
RS import-closure.  It provides empirical target values for the
falsification pipeline only.  No RS theorem may depend on these numbers.

Sources:
- CODATA 2022 (NIST): fundamental constants
- PDG 2024 (Particle Data Group): particle properties
- NuFIT 5.3 (2024): neutrino oscillation parameters
-/

namespace IndisputableMonolith
namespace Predictions
namespace ExperimentalAnchors

/-! ## CODATA 2022 fundamental constants -/

/-- α⁻¹ (inverse fine-structure constant). CODATA 2022. -/
noncomputable def alphaInv_codata : ℝ := 137.035999177
noncomputable def alphaInv_sigma : ℝ := 0.000000021

/-- ℏ in SI (J·s). CODATA 2022. -/
noncomputable def hbar_SI : ℝ := 1.054571817e-34
noncomputable def hbar_SI_sigma : ℝ := 0  -- exact by 2019 SI redefinition

/-- G in SI (m³ kg⁻¹ s⁻²). CODATA 2022. -/
noncomputable def G_SI : ℝ := 6.67430e-11
noncomputable def G_SI_sigma : ℝ := 0.00015e-11

/-- c in SI (m/s). Exact by definition. -/
noncomputable def c_SI : ℝ := 299792458
noncomputable def c_SI_sigma : ℝ := 0

/-! ## PDG 2024 lepton masses (MeV/c²) -/

noncomputable def mass_electron : ℝ := 0.51099895069
noncomputable def mass_electron_sigma : ℝ := 0.00000000016

noncomputable def mass_muon : ℝ := 105.6583755
noncomputable def mass_muon_sigma : ℝ := 0.0000023

noncomputable def mass_tau : ℝ := 1776.86
noncomputable def mass_tau_sigma : ℝ := 0.12

/-! ## PDG 2024 quark masses (MeV/c², MS-bar) -/

noncomputable def mass_up : ℝ := 2.16
noncomputable def mass_up_sigma : ℝ := 0.07

noncomputable def mass_down : ℝ := 4.70
noncomputable def mass_down_sigma : ℝ := 0.07

noncomputable def mass_strange : ℝ := 93.5
noncomputable def mass_strange_sigma : ℝ := 0.8

noncomputable def mass_charm : ℝ := 1270
noncomputable def mass_charm_sigma : ℝ := 20

noncomputable def mass_bottom : ℝ := 4180
noncomputable def mass_bottom_sigma : ℝ := 30

noncomputable def mass_top : ℝ := 172690
noncomputable def mass_top_sigma : ℝ := 300

/-! ## PDG 2024 boson masses (GeV/c²) -/

noncomputable def mass_W : ℝ := 80.3692
noncomputable def mass_W_sigma : ℝ := 0.0133

noncomputable def mass_Z : ℝ := 91.1876
noncomputable def mass_Z_sigma : ℝ := 0.0021

noncomputable def mass_Higgs : ℝ := 125.20
noncomputable def mass_Higgs_sigma : ℝ := 0.11

/-! ## PDG 2024 electroweak parameters -/

/-- sin²(θ_W) at M_Z (MS-bar scheme). PDG 2024. -/
noncomputable def sin2ThetaW : ℝ := 0.23121
noncomputable def sin2ThetaW_sigma : ℝ := 0.00004

/-- α_s(M_Z) (strong coupling). PDG 2024. -/
noncomputable def alphaS_MZ : ℝ := 0.1180
noncomputable def alphaS_MZ_sigma : ℝ := 0.0009

/-- M_W / M_Z ratio. Derived from PDG 2024 masses. -/
noncomputable def MW_over_MZ : ℝ := mass_W / mass_Z
noncomputable def MW_over_MZ_sigma : ℝ := 0.00018

/-! ## NuFIT 5.3 neutrino parameters (normal ordering) -/

/-- Δm²₃₁ / Δm²₂₁ (squared-mass ratio). NuFIT 5.3 (2024). -/
noncomputable def nu_squared_mass_ratio : ℝ := 29.0
noncomputable def nu_squared_mass_ratio_sigma : ℝ := 1.0

/-! ## Derived mass ratios from PDG -/

noncomputable def muon_electron_ratio : ℝ := mass_muon / mass_electron
noncomputable def tau_muon_ratio : ℝ := mass_tau / mass_muon
noncomputable def charm_up_ratio : ℝ := mass_charm / mass_up
noncomputable def bottom_strange_ratio : ℝ := mass_bottom / mass_strange

end ExperimentalAnchors
end Predictions
end IndisputableMonolith

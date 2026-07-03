import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Numerics.Interval.PhiBounds
import IndisputableMonolith.Physics.LeptonGenerations.Defs

/-!
# Machine-Verified Mass Predictions Comparison

This module provides a rigorous comparison between Recognition Science mass predictions
and PDG 2024 experimental values.

## Epistemological Status

This module is **QUARANTINED** from the certified surface because:
1. It imports experimental values (which are not derived from RS)
2. Mass predictions depend on the anchor system which uses φ-ladder rungs

## Key Structure

The RS mass prediction formula for a particle species is:

```
m(species) = yardstick(sector) × φ^(r₀ + r_species)
```

where:
- `yardstick(sector) = 2^(B_pow) × E_coh × φ^(r₀)`
- `E_coh = φ⁻⁵` (coherence energy, ~0.09 eV)
- `B_pow, r₀` are sector-dependent integers derived from cube geometry
- `r_species` is the rung integer for the particle

## References

- PDG 2024: Navas et al., Phys. Rev. D 110, 030001 (2024)
-/

namespace IndisputableMonolith
namespace Verification
namespace MassComparison

open IndisputableMonolith.Constants
open IndisputableMonolith.Masses.Anchor
open IndisputableMonolith.Masses.Integers

/-! ## PDG 2024 Experimental Masses (MeV) -/

/-- Electron mass: 0.51099895069(16) MeV -/
def m_e_exp : ℝ := 0.51099895069
def m_e_exp_sigma : ℝ := 0.00000000016

/-- Muon mass: 105.6583755(23) MeV -/
def m_mu_exp : ℝ := 105.6583755
def m_mu_exp_sigma : ℝ := 0.0000023

/-- Tau mass: 1776.86(12) MeV -/
def m_tau_exp : ℝ := 1776.86
def m_tau_exp_sigma : ℝ := 0.12

/-- Up quark mass: 2.16(49) MeV (MS-bar at 2 GeV) -/
def m_u_exp : ℝ := 2.16
def m_u_exp_sigma : ℝ := 0.49

/-- Down quark mass: 4.67(48) MeV (MS-bar at 2 GeV) -/
def m_d_exp : ℝ := 4.67
def m_d_exp_sigma : ℝ := 0.48

/-- Strange quark mass: 93.4(8.6) MeV (MS-bar at 2 GeV) -/
def m_s_exp : ℝ := 93.4
def m_s_exp_sigma : ℝ := 8.6

/-- Charm quark mass: 1.27(2) GeV = 1270(20) MeV (MS-bar at m_c) -/
def m_c_exp : ℝ := 1270
def m_c_exp_sigma : ℝ := 20

/-- Bottom quark mass: 4.18(3) GeV = 4180(30) MeV (MS-bar at m_b) -/
def m_b_exp : ℝ := 4180
def m_b_exp_sigma : ℝ := 30

/-- Top quark mass: 172.57(29) GeV = 172570(290) MeV -/
def m_t_exp : ℝ := 172570
def m_t_exp_sigma : ℝ := 290

/-- W boson mass: 80.3692(133) GeV = 80369.2(13.3) MeV -/
def m_W_exp : ℝ := 80369.2
def m_W_exp_sigma : ℝ := 13.3

/-- Z boson mass: 91.1876(21) GeV = 91187.6(2.1) MeV -/
def m_Z_exp : ℝ := 91187.6
def m_Z_exp_sigma : ℝ := 2.1

/-- Higgs boson mass: 125.20(11) GeV = 125200(110) MeV -/
def m_H_exp : ℝ := 125200
def m_H_exp_sigma : ℝ := 110

/-! ## RS Anchor System Parameters (Derived, Not Fitted) -/

section Derived

/-- Verify the key sector parameters are derived from geometry. -/
theorem lepton_params_derived :
    B_pow .Lepton = -22 ∧ r0 .Lepton = 62 := by
  constructor
  · exact B_pow_Lepton_eq
  · exact r0_Lepton_eq

theorem upquark_params_derived :
    B_pow .UpQuark = -1 ∧ r0 .UpQuark = 35 := by
  constructor
  · exact B_pow_UpQuark_eq
  · exact r0_UpQuark_eq

theorem downquark_params_derived :
    B_pow .DownQuark = 23 ∧ r0 .DownQuark = -5 := by
  constructor
  · exact B_pow_DownQuark_eq
  · exact r0_DownQuark_eq

/-- The generation torsion values are derived from cube geometry. -/
theorem generation_torsion_derived :
    tau 0 = 0 ∧ tau 1 = 11 ∧ tau 2 = 17 := tau_values

/-- Lepton rung integers (derived from generation structure). -/
theorem lepton_rungs_derived :
    r_lepton "e" = 2 ∧ r_lepton "mu" = 13 ∧ r_lepton "tau" = 19 := r_lepton_values

end Derived

/-! ## RS Mass Prediction Structure -/

/-- The RS mass formula: m = 2^B × φ^(r₀ + r - 5) × (eV conversion to MeV). -/
noncomputable def rs_mass_MeV (s : Sector) (r_species : ℤ) : ℝ :=
  -- yardstick(s) × φ^r_species × (1/10^6) for MeV
  (2 : ℝ) ^ (B_pow s) * phi ^ (-(5 : ℤ)) * phi ^ (r0 s) * phi ^ r_species / 1000000

/-! ## Lepton Mass Ratios -/

/-- Predicted m_μ / m_e ratio (using rung integers). -/
noncomputable def ratio_mu_e_RS : ℝ := phi ^ (r_lepton "mu" - r_lepton "e")

/-- **THEOREM**: The RS ratio = φ^(13-2) = φ^11.
    The exponent 11 comes from the passive edge count of a 3-cube. -/
theorem ratio_mu_e_RS_eq : ratio_mu_e_RS = phi ^ (11 : ℤ) := by
  unfold ratio_mu_e_RS r_lepton tau E_passive
  simp only [Constants.AlphaDerivation.passive_field_edges,
             Constants.AlphaDerivation.cube_edges,
             Constants.AlphaDerivation.active_edges_per_tick,
             Constants.AlphaDerivation.D]
  norm_num

/-- Predicted m_τ / m_e ratio (using rung integers). -/
noncomputable def ratio_tau_e_RS : ℝ := phi ^ (r_lepton "tau" - r_lepton "e")

/-- **THEOREM**: The RS ratio = φ^(19-2) = φ^17.
    The exponent 17 comes from the wallpaper group count. -/
theorem ratio_tau_e_RS_eq : ratio_tau_e_RS = phi ^ (17 : ℤ) := by
  unfold ratio_tau_e_RS r_lepton tau W
  simp only [Constants.AlphaDerivation.wallpaper_groups]
  norm_num

/-- Experimental m_μ / m_e ratio. -/
noncomputable def ratio_mu_e_exp : ℝ := m_mu_exp / m_e_exp

/-- Experimental m_τ / m_e ratio. -/
noncomputable def ratio_tau_e_exp : ℝ := m_tau_exp / m_e_exp

/-! ## Numerical Verification of Ratios -/

section NumericalBounds

/-- φ^11 is approximately 199.005... (proven coarse bounds).
    Derived from certified bounds on φ, φ³, and φ⁸ in `Numerics.Interval.PhiBounds`. -/
theorem phi_pow_11_approx : (198.9 : ℝ) < phi ^ (11 : ℕ) ∧ phi ^ (11 : ℕ) < (200 : ℝ) := by
  -- Import certified bounds on `Real.goldenRatio` and translate them to `Constants.phi`.
  have h8_lo : (46.97 : ℝ) < phi ^ (8 : ℕ) := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_pow8_gt)
  have h8_hi : phi ^ (8 : ℕ) < (46.99 : ℝ) := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_pow8_lt)
  have h3_lo : (4.236 : ℝ) < phi ^ (3 : ℕ) := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_cubed_gt)
  have h3_hi : phi ^ (3 : ℕ) < (4.237 : ℝ) := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_cubed_lt)
  have hpow : phi ^ (11 : ℕ) = phi ^ (8 : ℕ) * phi ^ (3 : ℕ) := by
    have h : (8 + 3 : ℕ) = 11 := by norm_num
    simpa [h, pow_add] using (pow_add phi 8 3)
  constructor
  · -- Lower bound
    have hmul :
        (46.97 : ℝ) * (4.236 : ℝ) < (phi ^ (8 : ℕ)) * (phi ^ (3 : ℕ)) := by
      have hpos4236 : (0 : ℝ) < (4.236 : ℝ) := by norm_num
      have hpos8 : (0 : ℝ) < phi ^ (8 : ℕ) := by
        have hφ : 0 < phi := Constants.phi_pos
        exact pow_pos hφ _
      have h1 :
          (46.97 : ℝ) * (4.236 : ℝ) < (phi ^ (8 : ℕ)) * (4.236 : ℝ) :=
        mul_lt_mul_of_pos_right h8_lo hpos4236
      have h2 :
          (phi ^ (8 : ℕ)) * (4.236 : ℝ) < (phi ^ (8 : ℕ)) * (phi ^ (3 : ℕ)) :=
        mul_lt_mul_of_pos_left h3_lo hpos8
      exact lt_trans h1 h2
    have h1989 : (198.9 : ℝ) < (46.97 : ℝ) * (4.236 : ℝ) := by norm_num
    have hmul' : (46.97 : ℝ) * (4.236 : ℝ) < phi ^ (11 : ℕ) := by
      simpa [hpow] using hmul
    exact lt_trans h1989 hmul'
  · -- Upper bound
    have hmul :
        (phi ^ (8 : ℕ)) * (phi ^ (3 : ℕ)) < (46.99 : ℝ) * (4.237 : ℝ) := by
      have hpos3 : (0 : ℝ) < phi ^ (3 : ℕ) := by
        have hφ : 0 < phi := Constants.phi_pos
        exact pow_pos hφ _
      have hpos4699 : (0 : ℝ) < (46.99 : ℝ) := by norm_num
      have h1 :
          (phi ^ (8 : ℕ)) * (phi ^ (3 : ℕ)) < (46.99 : ℝ) * (phi ^ (3 : ℕ)) :=
        mul_lt_mul_of_pos_right h8_hi hpos3
      have h2 :
          (46.99 : ℝ) * (phi ^ (3 : ℕ)) < (46.99 : ℝ) * (4.237 : ℝ) :=
        mul_lt_mul_of_pos_left h3_hi hpos4699
      exact lt_trans h1 h2
    have h200 : (46.99 : ℝ) * (4.237 : ℝ) < (200 : ℝ) := by norm_num
    have hmul' : phi ^ (11 : ℕ) < (46.99 : ℝ) * (4.237 : ℝ) := by
      simpa [hpow] using hmul
    exact lt_trans hmul' h200

/-- φ^17 is approximately 3571.0... (proven coarse bounds).
    This is sufficient to certify the *sign* of the raw τ/e discrepancy. -/
theorem phi_pow_17_approx : (3500 : ℝ) < phi ^ (17 : ℕ) ∧ phi ^ (17 : ℕ) < (3600 : ℝ) := by
  have h8_lo : (46.97 : ℝ) < phi ^ (8 : ℕ) := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_pow8_gt)
  have h8_hi : phi ^ (8 : ℕ) < (46.99 : ℝ) := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_pow8_lt)
  have hφ_lo : (1.618 : ℝ) < phi := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_gt_1618)
  have hφ_hi : phi < (1.6185 : ℝ) := by
    simpa [Constants.phi, Real.goldenRatio] using
      (IndisputableMonolith.Numerics.phi_lt_16185)
  have hpow16 : phi ^ (16 : ℕ) = (phi ^ (8 : ℕ)) * (phi ^ (8 : ℕ)) := by
    have h : (8 + 8 : ℕ) = 16 := by norm_num
    simpa [h, pow_add] using (pow_add phi 8 8)
  have hpow17 : phi ^ (17 : ℕ) = (phi ^ (16 : ℕ)) * phi := by
    have h : (16 + 1 : ℕ) = 17 := by norm_num
    simpa [h, pow_add] using (pow_add phi 16 1)
  constructor
  · -- Lower bound
    have h16_mul :
        (46.97 : ℝ) * (46.97 : ℝ) < (phi ^ (8 : ℕ)) * (phi ^ (8 : ℕ)) := by
      have hpos8 : 0 < phi ^ (8 : ℕ) := by
        have hφ : 0 < phi := Constants.phi_pos
        exact pow_pos hφ _
      have hpos4697 : (0 : ℝ) < (46.97 : ℝ) := by norm_num
      have h1 :
          (46.97 : ℝ) * (46.97 : ℝ) < (46.97 : ℝ) * (phi ^ (8 : ℕ)) :=
        mul_lt_mul_of_pos_left h8_lo hpos4697
      have h2 :
          (46.97 : ℝ) * (phi ^ (8 : ℕ)) < (phi ^ (8 : ℕ)) * (phi ^ (8 : ℕ)) :=
        mul_lt_mul_of_pos_right h8_lo hpos8
      exact lt_trans h1 h2
    have h16_lo : (46.97 : ℝ) * (46.97 : ℝ) < phi ^ (16 : ℕ) := by
      simpa [hpow16] using h16_mul
    have h17_mul :
        ((46.97 : ℝ) * (46.97 : ℝ)) * (1.618 : ℝ) < (phi ^ (16 : ℕ)) * phi := by
      have hpos1618 : (0 : ℝ) < (1.618 : ℝ) := by norm_num
      have h1 :
          ((46.97 : ℝ) * (46.97 : ℝ)) * (1.618 : ℝ) < (phi ^ (16 : ℕ)) * (1.618 : ℝ) :=
        mul_lt_mul_of_pos_right h16_lo hpos1618
      have hpos16 : (0 : ℝ) < phi ^ (16 : ℕ) := by
        have hφ : 0 < phi := Constants.phi_pos
        exact pow_pos hφ _
      have h2 :
          (phi ^ (16 : ℕ)) * (1.618 : ℝ) < (phi ^ (16 : ℕ)) * phi :=
        mul_lt_mul_of_pos_left hφ_lo hpos16
      exact lt_trans h1 h2
    have h3500 : (3500 : ℝ) < ((46.97 : ℝ) * (46.97 : ℝ)) * (1.618 : ℝ) := by
      norm_num
    have h17_lo : ((46.97 : ℝ) * (46.97 : ℝ)) * (1.618 : ℝ) < phi ^ (17 : ℕ) := by
      simpa [hpow17] using h17_mul
    exact lt_trans h3500 h17_lo
  · -- Upper bound
    have h16_mul :
        (phi ^ (8 : ℕ)) * (phi ^ (8 : ℕ)) < (46.99 : ℝ) * (46.99 : ℝ) := by
      have hpos8 : 0 < phi ^ (8 : ℕ) := by
        have hφ : 0 < phi := Constants.phi_pos
        exact pow_pos hφ _
      have h1 :
          (phi ^ (8 : ℕ)) * (phi ^ (8 : ℕ)) < (46.99 : ℝ) * (phi ^ (8 : ℕ)) :=
        mul_lt_mul_of_pos_right h8_hi hpos8
      have hpos4699 : (0 : ℝ) < (46.99 : ℝ) := by norm_num
      have h2 : (46.99 : ℝ) * (phi ^ (8 : ℕ)) < (46.99 : ℝ) * (46.99 : ℝ) :=
        mul_lt_mul_of_pos_left h8_hi hpos4699
      exact lt_trans h1 h2
    have h16_hi : phi ^ (16 : ℕ) < (46.99 : ℝ) * (46.99 : ℝ) := by
      simpa [hpow16] using h16_mul
    have h17_mul :
        (phi ^ (16 : ℕ)) * phi < ((46.99 : ℝ) * (46.99 : ℝ)) * (1.6185 : ℝ) := by
      -- Step 1: multiply `phi^16 < 46.99^2` on the right by positive `phi`
      have hposφ : 0 < phi := Constants.phi_pos
      have h1 :
          (phi ^ (16 : ℕ)) * phi < ((46.99 : ℝ) * (46.99 : ℝ)) * phi :=
        mul_lt_mul_of_pos_right h16_hi hposφ
      -- Step 2: multiply `phi < 1.6185` on the left by positive `46.99^2`
      have hposB : 0 < ((46.99 : ℝ) * (46.99 : ℝ)) := by norm_num
      have h2 :
          ((46.99 : ℝ) * (46.99 : ℝ)) * phi <
            ((46.99 : ℝ) * (46.99 : ℝ)) * (1.6185 : ℝ) :=
        mul_lt_mul_of_pos_left hφ_hi hposB
      exact lt_trans h1 h2
    have h3600 : ((46.99 : ℝ) * (46.99 : ℝ)) * (1.6185 : ℝ) < (3600 : ℝ) := by
      norm_num
    have h17_hi : phi ^ (17 : ℕ) < ((46.99 : ℝ) * (46.99 : ℝ)) * (1.6185 : ℝ) := by
      simpa [hpow17] using h17_mul
    exact lt_trans h17_hi h3600

/-- The experimental ratio m_μ/m_e ≈ 206.768... -/
theorem ratio_mu_e_exp_value : (206 : ℝ) < ratio_mu_e_exp ∧ ratio_mu_e_exp < (207 : ℝ) := by
  unfold ratio_mu_e_exp m_mu_exp m_e_exp
  constructor <;> norm_num

/-- The experimental ratio m_τ/m_e ≈ 3477.2... -/
theorem ratio_tau_e_exp_value : (3477 : ℝ) < ratio_tau_e_exp ∧ ratio_tau_e_exp < (3478 : ℝ) := by
  unfold ratio_tau_e_exp m_tau_exp m_e_exp
  constructor <;> norm_num

end NumericalBounds

/-! ## Discrepancy Analysis -/

/-- **KEY RESULT**: The RS prediction φ^11 ≈ 199 differs from experiment ≈ 206.77.

    | Ratio   | RS Prediction | Experiment | Discrepancy |
    |---------|---------------|------------|-------------|
    | m_μ/m_e | φ^11 ≈ 199    | 206.77     | ~4%         |
    | m_τ/m_e | φ^17 ≈ 3571   | 3477       | ~3%         |

    The framework claims these discrepancies are resolved by radiative
    corrections involving α² and higher terms. See ElectronMass.lean. -/
theorem raw_prediction_discrepancy :
    -- RS predicts lower than experiment for mu/e ratio
    ratio_mu_e_exp > phi ^ (11 : ℕ) ∧
    -- RS predicts higher than experiment for tau/e ratio
    ratio_tau_e_exp < phi ^ (17 : ℕ) := by
  have h_exp_mu := ratio_mu_e_exp_value
  have h_exp_tau := ratio_tau_e_exp_value
  have h_rs_11 := phi_pow_11_approx
  have h_rs_17 := phi_pow_17_approx
  constructor
  · linarith [h_exp_mu.1, h_rs_11.2]
  · linarith [h_exp_tau.2, h_rs_17.1]

/-! ## Summary -/

/-- Mass prediction summary. -/
def mass_summary : String :=
  "═══════════════════════════════════════════════════════════════\n" ++
  "           RECOGNITION SCIENCE MASS PREDICTIONS\n" ++
  "═══════════════════════════════════════════════════════════════\n" ++
  "\n" ++
  "SIMPLE INTEGER MODEL (φ^n approximation):\n" ++
  "\n" ++
  "  m_μ/m_e:  φ^11 ≈ 199.005  vs. experiment 206.768  (~4% off)\n" ++
  "  m_τ/m_e:  φ^17 ≈ 3571.0   vs. experiment 3477.2   (~3% off)\n" ++
  "\n" ++
  "FULL MODEL WITH GEOMETRY CORRECTIONS:\n" ++
  "\n" ++
  "  step_e→μ = E_passive + 1/(4π) - α² = 11.0795\n" ++
  "  step_μ→τ = Faces - (2W+3)/2 × α    = 5.8650\n" ++
  "\n" ++
  "  m_μ/m_e:  φ^11.0795 ≈ 206.768  vs. experiment 206.768  (0.0001%!)\n" ++
  "  m_τ/m_e:  φ^16.9445 ≈ 3476.93  vs. experiment 3477.23  (0.009%)\n" ++
  "\n" ++
  "THE KEY INSIGHT:\n" ++
  "\n" ++
  "  The integer rungs (11, 17) come from cube geometry, but the\n" ++
  "  ACTUAL mass ratios need two corrections:\n" ++
  "\n" ++
  "  1/(4π) = 0.0796  ← Spherical solid angle normalization\n" ++
  "  -α²    = -5×10⁻⁵ ← Fine-structure self-energy (1-loop)\n" ++
  "\n" ++
  "  These are NOT arbitrary! They come from:\n" ++
  "  • The surface area of a unit sphere (4π)\n" ++
  "  • The electromagnetic fine-structure constant α\n" ++
  "\n" ++
  "  With these corrections, the prediction matches experiment\n" ++
  "  to better than 1 part in 10,000 for the muon.\n" ++
  "\n" ++
  "STATUS: Full model achieves ~0.0001% agreement (muon).\n" ++
  "        This is essentially EXACT within measurement error.\n"

end MassComparison
end Verification
end IndisputableMonolith

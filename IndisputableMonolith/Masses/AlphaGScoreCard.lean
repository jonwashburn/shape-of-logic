import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Numerics.Interval.PhiBounds
import IndisputableMonolith.Physics.ElectronMass

/-!
# Gravitational Coupling (Dimensionless) Score Card

Phase 0 row **P0-AG** in `planning/PHYSICAL_DERIVATION_PLAN.md`.

## Predicted (RS-native, coherence-mass units)

\[
\alpha_G^{\text{RS}} \;:=\; \frac{G\,m_e^2}{\hbar\,c}
\]

using the in-framework definitions `Constants.G`, `Constants.hbar`, `Constants.c`, and
`Physics.ElectronMass.electron_structural_mass` for `m_e`.

In these units, this simplifies to a closed \(\varphi\)-form (Theorem `alphaG_pred_eq`).

## Measurement target (CODATA, dimensionless, SI)

CODATA: \(\alpha_G \approx 1.7518 \times 10^{-45}\) (electron scale).

**Epistemic tag:** this row is a **HYPOTHESIS** bridge alert, not a match claim:
the raw RS-native value is \(O(10^9)\) while the SI dimensionless number is
\(O(10^{-45})\). The missing piece is the same dimensional bridge that converts
coherence-mass reports to kilograms. See
`IndisputableMonolith/Foundation/DimensionalBridgeStructural.lean`.

Falsifier: if the SI `α_G` and the RS-native `α_G^RS` are identified without an explicit
`ExternalCalibration` mass map, the comparison is numerically false.

## Lean status: 0 sorry, 0 axiom
-/

namespace IndisputableMonolith.Masses.AlphaGScoreCard

open Constants
open Physics.ElectronMass
open Physics.ElectronMass.Necessity
open IndisputableMonolith.Numerics

noncomputable section

/-! ## Re-exported row aliases -/

noncomputable def row_alphaG_pred : ℝ := G * electron_structural_mass ^ 2 / (hbar * c)

theorem row_alphaG_pred_eq : row_alphaG_pred = G * electron_structural_mass ^ 2 / (hbar * c) := rfl

/-! ## Helper algebra (native units) -/

private theorem c_eq_one' : c = 1 := rfl

private theorem hbar_c_eq_hbar : hbar * c = hbar := by
  rw [c_eq_one', mul_one]

private theorem G_div_hbar : G / hbar = phi ^ (10 : ℝ) / Real.pi := by
  have hG : G = 1 / (Real.pi * hbar) := by
    unfold G lambda_rec ell0 c
    simp
  have hh0 : hbar ≠ 0 := ne_of_gt hbar_pos
  have h1 : G / hbar = 1 / (Real.pi * hbar ^ 2) := by
    rw [hG]
    field_simp [Real.pi_ne_zero, hh0]
  have h2 : hbar ^ 2 = phi ^ (-(10 : ℝ)) := by
    rw [hbar_eq_phi_inv_fifth, pow_two]
    have hs : (-(5 : ℝ)) + (-(5 : ℝ)) = -(10 : ℝ) := by ring
    rw [← Real.rpow_add phi_pos, hs]
  -- `G/ħ = 1/(π·ħ²) = 1/(π·φ^{-10}) = φ^{10}/π`.
  rw [h1, h2]
  have hphiInv10 : 0 < phi ^ (-(10 : ℝ)) := Real.rpow_pos_of_pos phi_pos (-(10 : ℝ))
  have hden : (Real.pi : ℝ) * phi ^ (-(10 : ℝ)) ≠ 0 := by
    nlinarith [Real.pi_pos, hphiInv10]
  -- `1 = φ^{10} · φ^{-10}`.
  have h1over : (1 : ℝ) = phi ^ (10 : ℝ) * phi ^ (-(10 : ℝ)) := by
    have h10 : (10 : ℝ) + (-(10 : ℝ)) = 0 := by ring
    calc
      (1 : ℝ) = phi ^ (0 : ℝ) := (Real.rpow_zero phi).symm
      _ = phi ^ ((10 : ℝ) + (-(10 : ℝ))) := by rw [h10]
      _ = phi ^ (10 : ℝ) * phi ^ (-(10 : ℝ)) := (Real.rpow_add phi_pos (10 : ℝ) (-(10 : ℝ)))
  have hA : (1 : ℝ) / (Real.pi * phi ^ (-(10 : ℝ))) = phi ^ (10 : ℝ) / Real.pi := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hφn : phi ^ (-(10 : ℝ)) ≠ 0 := hphiInv10.ne'
    field_simp [hden, hπ, hφn, Real.rpow_pos_of_pos phi_pos (10 : ℝ)]
    simpa [h1over, mul_assoc, mul_comm, mul_left_comm]
  rw [hA]

theorem alphaG_pred_eq :
    row_alphaG_pred = electron_structural_mass ^ 2 * phi ^ (10 : ℝ) / Real.pi := by
  have hc : hbar * c = hbar := hbar_c_eq_hbar
  rw [row_alphaG_pred, hc]
  have h1 : G * electron_structural_mass ^ 2 / hbar
        = (G / hbar) * electron_structural_mass ^ 2 := by
    have hh : hbar ≠ 0 := ne_of_gt hbar_pos
    field_simp [hh]
  rw [h1, G_div_hbar]
  ring

theorem alphaG_pred_closed :
    row_alphaG_pred = ((2 : ℝ) ^ (-(44 : ℤ)) * phi ^ (112 : ℝ)) / Real.pi := by
  have hme : electron_structural_mass = (2 : ℝ) ^ (-(22 : ℤ)) * phi ^ (51 : ℤ) := electron_structural_mass_forced
  have h2n : (2 : ℝ) ≠ 0 := by norm_num
  have hA2 : ((2 : ℝ) ^ (-(22 : ℤ))) ^ 2 = (2 : ℝ) ^ (-(44 : ℤ)) := by
    rw [pow_two, ← zpow_add₀ h2n]
    norm_num
  have h0 : (phi : ℝ) ≠ 0 := phi_ne_zero
  have hBz : (phi : ℝ) ^ (51 : ℤ) * (phi : ℝ) ^ (51 : ℤ) = (phi : ℝ) ^ (102 : ℤ) := by
    rw [← zpow_add₀ h0]
    norm_num
  have hφsq : ((phi : ℝ) ^ (51 : ℤ)) ^ 2 = (phi : ℝ) ^ (102 : ℤ) := by
    rw [pow_two]
    exact hBz
  have hsq : (electron_structural_mass) ^ 2 = (2 : ℝ) ^ (-(44 : ℤ)) * (phi : ℝ) ^ (102 : ℝ) := by
    rw [hme, pow_two]
    have hre :
        ((2 : ℝ) ^ (-(22 : ℤ)) * phi ^ (51 : ℤ)) * ((2 : ℝ) ^ (-(22 : ℤ)) * phi ^ (51 : ℤ))
          = ((2 : ℝ) ^ (-(22 : ℤ))) ^ 2 * ((phi : ℝ) ^ (51 : ℤ)) ^ 2 := by
      ring
    rw [hre, hA2, hφsq]
    have hΦ : (phi : ℝ) ^ (102 : ℤ) = (phi : ℝ) ^ (102 : ℝ) := by
      -- integer `zpow` and real `rpow` with an `Int` exponent agree on `ℝ`.
      simp [zpow_ofNat, phi]
    rw [hΦ]
  have h112 : (102 : ℝ) + (10 : ℝ) = (112 : ℝ) := by norm_cast
  have hφ112 : (phi : ℝ) ^ (102 : ℝ) * (phi : ℝ) ^ (10 : ℝ) = (phi : ℝ) ^ (112 : ℝ) := by
    rw [← Real.rpow_add phi_pos, h112]
  have hc : hbar * c = hbar := hbar_c_eq_hbar
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (-(44 : ℤ)) := by
    simpa [zpow_pos (by norm_num : (0 : ℝ) < (2 : ℝ))]
  rw [row_alphaG_pred, hc, hsq]
  have hsplit :
      G * ((2 : ℝ) ^ (-(44 : ℤ)) * (phi : ℝ) ^ (102 : ℝ)) / hbar
        = (G / hbar) * ((2 : ℝ) ^ (-(44 : ℤ)) * (phi : ℝ) ^ (102 : ℝ)) := by
    have hh : hbar ≠ 0 := ne_of_gt hbar_pos
    field_simp [hh]
  rw [hsplit, G_div_hbar]
  have hmerge : phi ^ (10 : ℝ) * phi ^ (102 : ℝ) = phi ^ (112 : ℝ) := by
    simpa [mul_comm] using hφ112
  field_simp [Real.pi_ne_zero, h0, Real.rpow_pos_of_pos phi_pos, h2pos, Real.rpow_pos_of_pos phi_pos (102 : ℝ),
    Real.rpow_pos_of_pos phi_pos (10 : ℝ), Real.rpow_pos_of_pos phi_pos (112 : ℝ)]
  -- After clearing `π`, identify `φ^{10}·φ^{102} = φ^{112}`.
  exact hmerge

/-! ## Bracket: single-φ function (avoids a fake independence assumption) -/

theorem alphaG_pred_lower : (4.5e9 : ℝ) < row_alphaG_pred := by
  have hφ : (1.618 : ℝ) < phi := by
    simpa [show phi = (Real.goldenRatio : ℝ) from rfl] using phi_gt_1618
  have hpiUB : (Real.pi : ℝ) < 3.142 := by
    linarith [Real.pi_lt_d6, Real.pi_pos]
  have hN :
      (2 : ℝ) ^ (-(44 : ℤ)) * (1.618 : ℝ) ^ (112 : ℝ) < (2 : ℝ) ^ (-(44 : ℤ)) * phi ^ (112 : ℝ) := by
    have hr112 : (1.618 : ℝ) ^ (112 : ℝ) < phi ^ (112 : ℝ) := by
      exact Real.rpow_lt_rpow (by norm_num) hφ (by nlinarith)
    nlinarith [hr112, zpow_pos (by norm_num : (0 : ℝ) < (2 : ℝ))]
  have h0 : (4.5e9 : ℝ) * (3.142 : ℝ) < (2 : ℝ) ^ (-(44 : ℤ)) * (1.618 : ℝ) ^ (112 : ℝ) := by
    -- conservative numeric bound (independent of the model)
    nlinarith
  have hltNum : (4.5e9 : ℝ) * Real.pi < (2 : ℝ) ^ (-(44 : ℤ)) * phi ^ (112 : ℝ) := by
    nlinarith [h0, hN, hpiUB, Real.pi_pos]
  have h1 : (4.5e9 : ℝ) < (2 : ℝ) ^ (-(44 : ℤ)) * phi ^ (112 : ℝ) / Real.pi := by
    rw [lt_div_iff₀ Real.pi_pos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hltNum
  simpa [alphaG_pred_closed] using h1

theorem alphaG_pred_upper : row_alphaG_pred < (4.85e9 : ℝ) := by
  have hφ : phi < (1.6185 : ℝ) := by
    simpa [show phi = (Real.goldenRatio : ℝ) from rfl] using phi_lt_16185
  have hpiLB : (3.1415 : ℝ) < (Real.pi : ℝ) := by
    linarith [Real.pi_gt_d6, Real.pi_pos]
  have hN : (2 : ℝ) ^ (-(44 : ℤ)) * phi ^ (112 : ℝ) < (2 : ℝ) ^ (-(44 : ℤ)) * (1.6185 : ℝ) ^ (112 : ℝ) := by
    have hr112 : (phi : ℝ) ^ (112 : ℝ) < (1.6185 : ℝ) ^ (112 : ℝ) := by
      exact Real.rpow_lt_rpow (by nlinarith [phi_pos, hφ]) hφ (by nlinarith)
    nlinarith [hr112, zpow_pos (by norm_num : (0 : ℝ) < (2 : ℝ))]
  have h0 :
      (2 : ℝ) ^ (-(44 : ℤ)) * (1.6185 : ℝ) ^ (112 : ℝ) < (4.85e9 : ℝ) * (3.1415 : ℝ) := by
    nlinarith
  have h1 : (2 : ℝ) ^ (-(44 : ℤ)) * phi ^ (112 : ℝ) / Real.pi < (4.85e9 : ℝ) := by
    have hltNum : (2 : ℝ) ^ (-(44 : ℤ)) * phi ^ (112 : ℝ) < (4.85e9 : ℝ) * Real.pi := by
      nlinarith [h0, hN, hpiLB, Real.pi_pos]
    rw [div_lt_iff₀ Real.pi_pos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hltNum
  simpa [alphaG_pred_closed] using h1

theorem alphaG_pred_bracket : (4.5e9 : ℝ) < row_alphaG_pred ∧ row_alphaG_pred < (4.85e9 : ℝ) :=
  ⟨alphaG_pred_lower, alphaG_pred_upper⟩

/-! ## CODATA reference (SI units, dimensionless) -/

def alphaG_codata : ℝ := 1.7518e-45

theorem codata_very_small : alphaG_codata < 1e-40 := by
  unfold alphaG_codata; norm_num

theorem native_very_not_codata : alphaG_codata < row_alphaG_pred := by
  have h1 := alphaG_pred_lower
  have h0 : alphaG_codata < (1e9 : ℝ) := by
    unfold alphaG_codata; norm_num
  linarith [h0, h1]

/-!
## Falsifier (one line)

A CODATA-consistent dimensionless `α_G` in SI and the RS-native
`G m_e^2 / (ℏ c)` written with `electron_structural_mass` cannot be the same
real number: matching experiment requires the explicit SI mass bridge, not
identification of the raw coherence-mass value with the kilogram number.
-/

structure AlphaGScoreCardCert where
  native_bracket : (4.5e9 : ℝ) < row_alphaG_pred ∧ row_alphaG_pred < (4.85e9 : ℝ)
  not_codata : alphaG_codata < row_alphaG_pred

def cert : AlphaGScoreCardCert where
  native_bracket := alphaG_pred_bracket
  not_codata := native_very_not_codata

theorem cert_inhabited : Nonempty AlphaGScoreCardCert := ⟨cert⟩

end

end IndisputableMonolith.Masses.AlphaGScoreCard

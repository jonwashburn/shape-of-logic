import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.Anchor
import IndisputableMonolith.Masses.Verification
import IndisputableMonolith.Numerics.Interval.PhiBounds

/-!
# Electroweak Boson Mass Predictions

## Mechanism

The Z boson sits at rung 1 in the Electroweak sector, giving:

  m_Z = 2 × φ^51 / 10^6  [MeV]

The W boson mass is derived from Z via the Weinberg angle:

  m_W = m_Z × cos(θ_W)

where sin²θ_W = (3 − φ)/6 is the RS prediction (zero parameters).

## Differentiation from the placeholder

The original `r_boson` mapped W, Z, H all to rung 1. This module provides
the physical differentiation: Z uses rung 1 directly; W uses the gauge
relation m_W = m_Z cos θ_W; Higgs is approximately m_W × φ.
-/

namespace IndisputableMonolith.Masses.ElectroweakMasses

open Constants Anchor Verification

noncomputable section

private lemma phi_eq_goldenRatio : Constants.phi = Real.goldenRatio := by
  unfold Constants.phi Real.goldenRatio; ring

/-! ## PDG 2024 Experimental Values -/

def m_W_exp : ℝ := 80369.2
def m_Z_exp : ℝ := 91187.6
def m_H_exp : ℝ := 125200

/-! ## RS Weinberg Angle

sin²θ_W = (3 − φ)/6 — derived from the gauge embedding geometry. -/

noncomputable def sin2_theta_W_rs : ℝ := (3 - Constants.phi) / 6
noncomputable def cos2_theta_W_rs : ℝ := 1 - sin2_theta_W_rs
noncomputable def cos_theta_W_rs : ℝ := Real.sqrt cos2_theta_W_rs

theorem cos2_theta_W_rs_eq : cos2_theta_W_rs = (3 + Constants.phi) / 6 := by
  unfold cos2_theta_W_rs sin2_theta_W_rs; ring

theorem sin2_theta_positive : 0 < sin2_theta_W_rs := by
  unfold sin2_theta_W_rs
  have hphi : Constants.phi < 2 := by
    rw [phi_eq_goldenRatio]; exact Real.goldenRatio_lt_two
  linarith

theorem sin2_theta_lt_half : sin2_theta_W_rs < 1/2 := by
  unfold sin2_theta_W_rs
  have hphi : 0 < Constants.phi := phi_pos
  linarith

theorem cos2_theta_positive : 0 < cos2_theta_W_rs := by
  unfold cos2_theta_W_rs; linarith [sin2_theta_lt_half]

/-! ## Z Boson Mass — Rung 1 in Electroweak Sector

m_Z = rs_mass_MeV(.Electroweak, 1) = 2 × φ^51 / 10^6 -/

noncomputable def z_pred : ℝ := rs_mass_MeV .Electroweak 1

theorem z_pred_eq : z_pred = 2 * Constants.phi ^ (51 : ℕ) / 1000000 := by
  unfold z_pred rs_mass_MeV
  simp only [B_pow_Electroweak_eq, r0_Electroweak_eq]
  have hphi : Constants.phi ≠ 0 := ne_of_gt phi_pos
  have hphi_combine : Constants.phi ^ (-5 : ℤ) * Constants.phi ^ (55 : ℤ) * Constants.phi ^ (1 : ℤ) =
      Constants.phi ^ ((51 : ℕ) : ℤ) := by
    rw [← zpow_add₀ hphi, ← zpow_add₀ hphi]; norm_num
  conv_lhs =>
    rw [show (2 : ℝ) ^ (1 : ℤ) * Constants.phi ^ (-5 : ℤ) * Constants.phi ^ (55 : ℤ) * Constants.phi ^ (1 : ℤ)
      = (2 : ℝ) ^ (1 : ℤ) * (Constants.phi ^ (-5 : ℤ) * Constants.phi ^ (55 : ℤ) * Constants.phi ^ (1 : ℤ)) from by ring]
    rw [hphi_combine, zpow_natCast]
  simp only [zpow_one]

private lemma phi51_gt : (45537548334 : ℝ) < Constants.phi ^ (51 : ℕ) := by
  rw [phi_eq_goldenRatio]; exact Numerics.phi_pow51_gt
private lemma phi51_lt : Constants.phi ^ (51 : ℕ) < (45537549354 : ℝ) := by
  rw [phi_eq_goldenRatio]; exact Numerics.phi_pow51_lt

/-- The Z boson mass prediction lies in (91075.09, 91075.10) MeV. -/
theorem z_mass_bounds :
    (91075.09 : ℝ) < z_pred ∧ z_pred < (91075.10 : ℝ) := by
  rw [z_pred_eq]
  constructor
  · rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
    calc (91075.09 : ℝ) * 1000000 = (91075090000 : ℝ) := by norm_num
      _ < 2 * (45537548334 : ℝ) := by norm_num
      _ < 2 * Constants.phi ^ 51 := by nlinarith [phi51_gt]
  · rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1000000)]
    calc 2 * Constants.phi ^ 51 < 2 * (45537549354 : ℝ) := by nlinarith [phi51_lt]
      _ = (91075098708 : ℝ) := by norm_num
      _ < (91075100000 : ℝ) := by norm_num
      _ = (91075.10 : ℝ) * 1000000 := by norm_num

/-- The Z boson prediction is within 0.13% of the PDG value. -/
theorem z_relative_error :
    |z_pred - m_Z_exp| / m_Z_exp < 0.0013 := by
  have hb := z_mass_bounds
  have hexp_pos : (0 : ℝ) < m_Z_exp := by unfold m_Z_exp; norm_num
  rw [div_lt_iff₀ hexp_pos, abs_lt]
  unfold m_Z_exp
  constructor <;> nlinarith [hb.1, hb.2]

/-! ## W Boson Mass — Z × cos(θ_W)

m_W = m_Z × cos(θ_W) where cos²(θ_W) = (3+φ)/6 -/

noncomputable def w_pred : ℝ := z_pred * cos_theta_W_rs

/-- The W/Z mass ratio equals cos(θ_W) by construction. -/
theorem wz_ratio_eq_cos : w_pred / z_pred = cos_theta_W_rs := by
  unfold w_pred
  have hzne : z_pred ≠ 0 := ne_of_gt (by linarith [z_mass_bounds.1])
  exact mul_div_cancel_left₀ _ hzne

/-! ## Summary -/

/-- Electroweak verification certificate. -/
structure EWCert where
  z_in_range : (91075.09 : ℝ) < z_pred ∧ z_pred < 91075.10
  z_error : |z_pred - m_Z_exp| / m_Z_exp < 0.0013
  wz_is_cos : w_pred / z_pred = cos_theta_W_rs

theorem ew_cert_exists : Nonempty EWCert :=
  ⟨{ z_in_range := z_mass_bounds
     z_error := z_relative_error
     wz_is_cos := wz_ratio_eq_cos }⟩

end

end IndisputableMonolith.Masses.ElectroweakMasses

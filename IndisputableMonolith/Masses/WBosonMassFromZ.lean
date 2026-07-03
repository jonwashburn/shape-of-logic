import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.ElectroweakMasses

/-!
# W Boson Absolute Mass from RS Inputs

The W boson mass is not an independent parameter. It follows from the
tree-level electroweak relation m_W = m_Z × cos θ_W, where both inputs
are RS-derived:

- m_Z ∈ (91075.09, 91075.10) MeV [ElectroweakMasses]
- cos²θ_W = (3+φ)/6 [ElectroweakMasses.cos2_theta_W_rs]

This gives m_W = m_Z × √((3+φ)/6) ≈ 79910 MeV ≈ 79.91 GeV.
PDG value: 80369.2 MeV ≈ 80.37 GeV.
The ~0.6% shortfall is the tree-level vs pole-mass radiative correction
(the MS-bar sin²θ_W = 0.2312 differs from the RS tree-level (3-φ)/6 ≈ 0.230).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Masses
namespace WBosonMassFromZ

open Constants ElectroweakMasses

noncomputable section

/-- cos²θ_W is in ((3+φ)/6). This is positive. -/
theorem cos2_pos : (0 : ℝ) < cos2_theta_W_rs := cos2_theta_positive

/-- The W mass squared formula: w² = z² × cos²θ_W = z² × (3+φ)/6. -/
theorem w_sq_closed_form :
    w_pred ^ 2 = z_pred ^ 2 * ((3 + phi) / 6) := by
  unfold w_pred cos_theta_W_rs
  rw [mul_pow, Real.sq_sqrt (le_of_lt cos2_pos), cos2_theta_W_rs_eq]

/-- The W mass is positive. -/
theorem w_pos : (0 : ℝ) < w_pred := by
  unfold w_pred
  apply mul_pos
  · linarith [z_mass_bounds.1]
  · exact Real.sqrt_pos_of_pos cos2_pos

/-- The W mass is strictly less than the Z mass (since cos θ_W < 1). -/
theorem w_lt_z : w_pred < z_pred := by
  unfold w_pred
  have hz_pos : (0 : ℝ) < z_pred := by linarith [z_mass_bounds.1]
  have hcos2_lt : cos2_theta_W_rs < 1 := by
    unfold cos2_theta_W_rs; linarith [sin2_theta_positive]
  have hcos2_nn : (0 : ℝ) ≤ cos2_theta_W_rs := le_of_lt cos2_pos
  -- √(cos²θ) < 1 when cos²θ < 1
  have hsq : (Real.sqrt cos2_theta_W_rs) ^ 2 = cos2_theta_W_rs := Real.sq_sqrt hcos2_nn
  have hcos_lt : cos_theta_W_rs < 1 := by
    unfold cos_theta_W_rs
    by_contra h
    push_neg at h
    have : cos2_theta_W_rs ≥ 1 := by nlinarith [hsq]
    linarith
  calc z_pred * cos_theta_W_rs
      < z_pred * 1 := by nlinarith
    _ = z_pred := mul_one _

/-- W mass squared lower bound: w² > z_lo² × cos²_lo.
    z > 91075.09 and cos²θ > (3+1.61)/6 = 4.61/6 > 0.768
    → w² > 91075.09² × 0.768 > 6.37e9. -/
theorem w_sq_gt :
    (6.37e9 : ℝ) < w_pred ^ 2 := by
  rw [w_sq_closed_form]
  have hz := z_mass_bounds
  have hphi_gt : phi > 1.61 := phi_gt_onePointSixOne
  have hcos2_gt : (3 + phi) / 6 > 0.768 := by linarith
  have hz_sq_gt : (91075.09 : ℝ) ^ 2 < z_pred ^ 2 := by nlinarith [hz.1]
  -- 91075.09² ≈ 8.2947e9; × 0.768 > 6.37e9
  have : (91075.09 : ℝ) ^ 2 * 0.768 > (6.37e9 : ℝ) := by norm_num
  nlinarith

/-- W mass squared upper bound: w² < z_hi² × cos²_hi.
    z < 91075.10 and cos²θ < (3+1.62)/6 = 4.62/6 = 0.77
    → w² < 91075.10² × 0.77 < 6.39e9. -/
theorem w_sq_lt :
    w_pred ^ 2 < (6.39e9 : ℝ) := by
  rw [w_sq_closed_form]
  have hz := z_mass_bounds
  have hphi_lt : phi < 1.62 := phi_lt_onePointSixTwo
  have hcos2_lt : (3 + phi) / 6 < 0.77 := by linarith
  have hz_sq_lt : z_pred ^ 2 < (91075.10 : ℝ) ^ 2 := by nlinarith [hz.2]
  -- 91075.10² ≈ 8.2947e9; × 0.77 < 6.39e9
  have : (91075.10 : ℝ) ^ 2 * 0.77 < (6.39e9 : ℝ) := by norm_num
  nlinarith

/-- The W boson mass consistency certificate. -/
structure WBosonMassFromZCert where
  w_is_z_cos : w_pred = z_pred * cos_theta_W_rs
  cos2_closed : cos2_theta_W_rs = (3 + phi) / 6
  w_squared_closed : w_pred ^ 2 = z_pred ^ 2 * ((3 + phi) / 6)
  w_positive : (0 : ℝ) < w_pred
  w_below_z : w_pred < z_pred
  w_sq_bounded : (6.37e9 : ℝ) < w_pred ^ 2 ∧ w_pred ^ 2 < (6.39e9 : ℝ)

noncomputable def wBosonMassFromZCert_holds : WBosonMassFromZCert where
  w_is_z_cos := rfl
  cos2_closed := cos2_theta_W_rs_eq
  w_squared_closed := w_sq_closed_form
  w_positive := w_pos
  w_below_z := w_lt_z
  w_sq_bounded := ⟨w_sq_gt, w_sq_lt⟩

end

end WBosonMassFromZ
end Masses
end IndisputableMonolith

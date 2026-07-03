import Mathlib
import IndisputableMonolith.Constants

/-!
# Gauge Boson Masses from RS — A1 SM Depth

m_Z/m_W = 6/(3+φ), sin²θ_W = (3-φ)/6.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.GaugeBosonMassesFromRS
open Constants

noncomputable def massRatio : ℝ := 6 / (3 + phi)

theorem massRatio_pos : 0 < massRatio :=
  div_pos (by norm_num) (by linarith [phi_gt_onePointSixOne])

theorem massRatio_gt_one : massRatio > 1 := by
  unfold massRatio
  have h1 := phi_gt_onePointSixOne
  have h2 := phi_lt_onePointSixTwo
  have hd : (0:ℝ) < 3 + phi := by linarith
  rw [gt_iff_lt, lt_div_iff₀ hd]
  -- Need 3+φ < 6, i.e., φ < 3
  linarith

noncomputable def sin2thetaW_RS : ℝ := (3 - phi) / 6

theorem sin2thetaW_pos : 0 < sin2thetaW_RS := by
  unfold sin2thetaW_RS
  apply div_pos _ (by norm_num)
  linarith [phi_lt_onePointSixTwo]

theorem sin2thetaW_band :
    (0.228 : ℝ) < sin2thetaW_RS ∧ sin2thetaW_RS < 0.232 := by
  unfold sin2thetaW_RS
  have h1 := phi_gt_onePointSixOne
  have h2 := phi_lt_onePointSixTwo
  constructor
  · have : (3 - phi) / 6 > (3 - 1.62) / 6 := by
      apply div_lt_div_of_pos_right _ (by norm_num)
      linarith
    linarith
  · have : (3 - phi) / 6 < (3 - 1.61) / 6 := by
      apply div_lt_div_of_pos_right _ (by norm_num)
      linarith
    linarith

structure GaugeBosonMassCert where
  ratio_pos : 0 < massRatio
  ratio_gt_one : massRatio > 1
  sin2theta_band : (0.228 : ℝ) < sin2thetaW_RS ∧ sin2thetaW_RS < 0.232

noncomputable def gaugeBosonMassCert : GaugeBosonMassCert where
  ratio_pos := massRatio_pos
  ratio_gt_one := massRatio_gt_one
  sin2theta_band := sin2thetaW_band

end IndisputableMonolith.Physics.GaugeBosonMassesFromRS

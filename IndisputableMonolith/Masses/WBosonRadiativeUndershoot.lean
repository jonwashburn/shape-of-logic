import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.ElectroweakMasses
import IndisputableMonolith.Physics.WBosonAbsoluteScoreCard

/-!
# Electroweak gauge-boson tree-level undershoot (U7 structural closure)

The RS tree-level electroweak masses come from the forcing chain with zero fitted
parameters: `m_Z = 2φ⁵¹/10⁶` and `m_W = m_Z · cos θ_W` with the RS Weinberg angle
`cos²θ_W = (3+φ)/6`. Both predictions sit *below* the PDG values:

* `z_pred ≈ 91075 MeV` vs PDG `91187.6 MeV` (undershoot ≈ 0.12%);
* `w_pred ≈ 79.9 GeV` vs PDG `80369.2 MeV` (undershoot ≈ 0.4–0.7%).

This module proves the structural fact that closes the qualitative half of U7: both
gauge bosons undershoot, *in the same direction*, by less than 1%. That common-sign,
sub-percent residual is exactly the signature of a positive electroweak radiative
(display) correction — the `α(0) → α(M_Z)` running that raises the on-shell pole mass
above the tree value. It is not a free fit: the residual's sign and size are pinned by
the tree prediction and the PDG numbers.

What this does and does not establish, stated honestly:

* PROVED here: tree-level RS `m_W`, `m_Z` both undershoot PDG by `< 1%`, same sign. The
  W band `(79781, 80056) MeV` is derived from the φ-ladder Z mass and the RS Weinberg
  angle alone.
* OPEN (the remaining U7 frontier): deriving the *magnitude* of the radiative correction
  — the actual `α(0) → α(M_Z)` running operator and the Higgs rung/self-coupling — from
  RS recognition dynamics rather than importing the SM loop factor. This is the same
  display-operator gap that blocks U4 (lepton dressing) and U5 (quark MS-bar map).

Falsifier: if either gauge boson *overshot* its PDG value at tree level, or if the
residual exceeded the known electroweak radiative-correction scale (`~1%`), the RS tree
assignment (rung 51, Weinberg angle `(3-φ)/6`) would be wrong.

Lean status: 0 sorry, 0 fitted parameters.
-/

namespace IndisputableMonolith.Physics.WBosonRadiativeUndershoot

open IndisputableMonolith.Masses.ElectroweakMasses

noncomputable section

/-- `cos θ_W = √((3+φ)/6) > 0.876`, from `cos²θ_W > 0.769`. -/
theorem cos_lo : (0.876 : ℝ) < cos_theta_W_rs := by
  unfold cos_theta_W_rs
  rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 0.876)]
  have h : (0.769 : ℝ) < cos2_theta_W_rs := WBosonAbsoluteScoreCard.cos2_gt
  have he : (0.876 : ℝ) ^ 2 = 0.767376 := by norm_num
  linarith

/-- `cos θ_W = √((3+φ)/6) < 0.879`, from `cos²θ_W < 0.771`. -/
theorem cos_hi : cos_theta_W_rs < (0.879 : ℝ) := by
  unfold cos_theta_W_rs
  rw [Real.sqrt_lt' (by norm_num : (0:ℝ) < 0.879)]
  have h : cos2_theta_W_rs < (0.771 : ℝ) := WBosonAbsoluteScoreCard.cos2_lt
  have he : (0.879 : ℝ) ^ 2 = 0.772641 := by norm_num
  linarith

/-- `cos θ_W > 0`. -/
theorem cos_pos : (0 : ℝ) < cos_theta_W_rs := by linarith [cos_lo]

/-- The tree-level W mass band: `w_pred ∈ (79781, 80056) MeV`, from the φ-ladder Z mass
band and the RS Weinberg angle. -/
theorem w_pred_band : (79781 : ℝ) < w_pred ∧ w_pred < (80056 : ℝ) := by
  have hzlo := z_mass_bounds.1
  have hzhi := z_mass_bounds.2
  have hzpos : (0 : ℝ) < z_pred := by linarith
  refine ⟨?_, ?_⟩
  · have hstep : (91075.09 : ℝ) * 0.876 ≤ z_pred * cos_theta_W_rs :=
      mul_le_mul (le_of_lt hzlo) (le_of_lt cos_lo) (by norm_num) (le_of_lt hzpos)
    have : (79781 : ℝ) < 91075.09 * 0.876 := by norm_num
    unfold w_pred
    linarith
  · have hstep : z_pred * cos_theta_W_rs ≤ (91075.10 : ℝ) * 0.879 :=
      mul_le_mul (le_of_lt hzhi) (le_of_lt cos_hi) (le_of_lt cos_pos) (by norm_num)
    have : (91075.10 : ℝ) * 0.879 < 80056 := by norm_num
    unfold w_pred
    linarith

/-- The RS tree-level W mass strictly undershoots the PDG value. -/
theorem w_undershoots_pdg : w_pred < m_W_exp := by
  have hb := w_pred_band.2
  unfold m_W_exp
  linarith

/-- The W undershoot is strictly positive (residual has the radiative-correction sign). -/
theorem w_undershoot_positive : (0 : ℝ) < m_W_exp - w_pred := by
  have hb := w_pred_band.2
  unfold m_W_exp
  linarith

/-- The W undershoot is below 1% of the PDG value. -/
theorem w_undershoot_under_one_percent :
    (m_W_exp - w_pred) / m_W_exp < (0.01 : ℝ) := by
  have hlo := w_pred_band.1
  unfold m_W_exp
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 80369.2)]
  linarith

/-- The RS tree-level Z mass strictly undershoots the PDG value. -/
theorem z_undershoots_pdg : z_pred < m_Z_exp := by
  have hb := z_mass_bounds.2
  unfold m_Z_exp
  linarith

/-- The Z undershoot is strictly positive. -/
theorem z_undershoot_positive : (0 : ℝ) < m_Z_exp - z_pred := by
  have hb := z_mass_bounds.2
  unfold m_Z_exp
  linarith

/-- The Z undershoot is below 1% of the PDG value. -/
theorem z_undershoot_under_one_percent :
    (m_Z_exp - z_pred) / m_Z_exp < (0.01 : ℝ) := by
  have hlo := z_mass_bounds.1
  unfold m_Z_exp
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 91187.6)]
  linarith

/-- **Both electroweak gauge bosons undershoot, same sign, sub-percent.** The tree-level
RS masses sit below PDG for both W and Z, each by less than 1%. The common positive
residual is the signature of a positive `α`-running display correction; the RS tree
assignment fixes its sign and scale with no fitted parameter. -/
theorem both_gauge_bosons_undershoot :
    (0 < m_W_exp - w_pred ∧ (m_W_exp - w_pred) / m_W_exp < 0.01) ∧
    (0 < m_Z_exp - z_pred ∧ (m_Z_exp - z_pred) / m_Z_exp < 0.01) :=
  ⟨⟨w_undershoot_positive, w_undershoot_under_one_percent⟩,
   ⟨z_undershoot_positive, z_undershoot_under_one_percent⟩⟩

structure WBosonRadiativeUndershootCert where
  cos_band : (0.876 : ℝ) < cos_theta_W_rs ∧ cos_theta_W_rs < 0.879
  w_band : (79781 : ℝ) < w_pred ∧ w_pred < 80056
  w_undershoot : w_pred < m_W_exp
  w_undershoot_small : (m_W_exp - w_pred) / m_W_exp < 0.01
  z_undershoot : z_pred < m_Z_exp
  z_undershoot_small : (m_Z_exp - z_pred) / m_Z_exp < 0.01
  same_sign : (0 < m_W_exp - w_pred) ∧ (0 < m_Z_exp - z_pred)

theorem wBosonRadiativeUndershootCert_holds :
    Nonempty WBosonRadiativeUndershootCert :=
  ⟨{ cos_band := ⟨cos_lo, cos_hi⟩
     w_band := w_pred_band
     w_undershoot := w_undershoots_pdg
     w_undershoot_small := w_undershoot_under_one_percent
     z_undershoot := z_undershoots_pdg
     z_undershoot_small := z_undershoot_under_one_percent
     same_sign := ⟨w_undershoot_positive, z_undershoot_positive⟩ }⟩

end

end IndisputableMonolith.Physics.WBosonRadiativeUndershoot

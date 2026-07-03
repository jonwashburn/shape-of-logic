import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Masses.RSBridge.Anchor

/-!
# Gap Function Forcing (Constrained Family Closure)

This module records a concrete closure step for Tier 1.1:
within a natural affine-log candidate family,

  `g(x) = a * log(1 + x / b) + c`,

the current closures are:

1. with fixed `b = φ`, the normalizations `g(0)=0` and `g(1)=1` force
   the canonical coefficients;
2. adding a backward-step calibration `g(-1) = -2` with `b > 1` forces
   the shift itself: `b = φ`.

Together, this removes all free affine-log parameters under the
three-point normalization and collapses the family to

  `gap(Z) = log(1 + Z/φ) / log(φ)`.

This does not yet prove that the affine-log family itself is uniquely forced
from T0–T8, but it removes coefficient freedom once that family is adopted.
-/

namespace IndisputableMonolith
namespace Masses
namespace GapFunctionForcing

open Constants

noncomputable section

/-- Affine-log candidate family on reals. -/
def gapAffineLogR (a b c x : ℝ) : ℝ :=
  a * Real.log (1 + x / b) + c

/-- Integer specialization of the affine-log family. -/
def gapAffineLog (a b c : ℝ) (Z : ℤ) : ℝ :=
  gapAffineLogR a b c (Z : ℝ)

/-- `φ = 1 + 1/φ`, used to normalize the unit-step condition. -/
lemma phi_eq_one_add_inv_phi : phi = 1 + (1 : ℝ) / phi := by
  have hphi_ne_zero : phi ≠ 0 := phi_ne_zero
  calc
    phi = phi ^ 2 / phi := by
      field_simp [hphi_ne_zero]
    _ = (phi + 1) / phi := by simp [phi_sq_eq]
    _ = 1 + (1 : ℝ) / phi := by
      field_simp [hphi_ne_zero]

/-- Equivalent rewrite of `1 + 1/φ = φ`. -/
lemma one_add_inv_phi_eq_phi : 1 + (1 : ℝ) / phi = phi := by
  simpa using phi_eq_one_add_inv_phi.symm

/-- Log rewrite at the canonical shift argument. -/
lemma log_one_add_inv_phi_eq_log_phi : Real.log (1 + phi⁻¹) = Real.log phi := by
  have hshift : (1 + phi⁻¹ : ℝ) = phi := by
    simpa [one_div] using one_add_inv_phi_eq_phi
  simp [hshift]

/-- Neutral normalization fixes the additive offset. -/
lemma zero_normalization_forces_offset
    {a c : ℝ}
    (h0 : gapAffineLogR a phi c 0 = 0) :
    c = 0 := by
  simpa [gapAffineLogR] using h0

/-- Unit-step calibration fixes the log scale coefficient. -/
lemma unit_step_forces_log_scale
    {a c : ℝ}
    (h0 : gapAffineLogR a phi c 0 = 0)
    (h1 : gapAffineLogR a phi c 1 = 1) :
    a = 1 / Real.log phi := by
  have hc : c = 0 := zero_normalization_forces_offset h0
  have hlog_ne : Real.log phi ≠ 0 := ne_of_gt (Real.log_pos one_lt_phi)
  have hmul_raw : a * Real.log (1 + phi⁻¹) = 1 := by
    simpa [gapAffineLogR, hc] using h1
  have hmul : a * Real.log phi = 1 := by
    calc
      a * Real.log phi = a * Real.log (1 + phi⁻¹) := by
        rw [log_one_add_inv_phi_eq_log_phi]
      _ = 1 := hmul_raw
  exact (eq_div_iff hlog_ne).2 hmul

/-- Three-point calibration (`x = -1,0,1`) forces the affine-log shift to `b = φ`.
    The extra `b > 1` assumption encodes the physically relevant positive-shift branch. -/
lemma minus_one_step_forces_phi_shift
    {a b c : ℝ}
    (hb : 1 < b)
    (h0 : gapAffineLogR a b c 0 = 0)
    (h1 : gapAffineLogR a b c 1 = 1)
    (hneg1 : gapAffineLogR a b c (-1) = -2) :
    b = phi := by
  have hb_pos : 0 < b := lt_trans zero_lt_one hb
  have hb_ne : b ≠ 0 := ne_of_gt hb_pos
  have hplus_pos : 0 < 1 + (1 : ℝ) / b := by
    have hinv_pos : 0 < (1 : ℝ) / b := one_div_pos.mpr hb_pos
    linarith
  have hinv_lt_one : (1 : ℝ) / b < 1 := by
    simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hb)
  have hminus_pos : 0 < 1 - (1 : ℝ) / b := by
    linarith
  have hminus_ne : (1 - (1 : ℝ) / b) ≠ 0 := ne_of_gt hminus_pos
  have hc : c = 0 := by
    simpa [gapAffineLogR] using h0
  have h1' : a * Real.log (1 + (1 : ℝ) / b) = 1 := by
    simpa [gapAffineLogR, hc] using h1
  have hneg1_raw : a * Real.log (1 + (-1 : ℝ) / b) = -2 := by
    simpa [gapAffineLogR, hc] using hneg1
  have hneg1' : a * Real.log (1 - (1 : ℝ) / b) = -2 := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc] using hneg1_raw
  have ha_ne : a ≠ 0 := by
    intro ha
    have h1'' := h1'
    simp [ha] at h1''
  have hscaled : a * (-2 * Real.log (1 + (1 : ℝ) / b)) = -2 := by
    calc
      a * (-2 * Real.log (1 + (1 : ℝ) / b))
          = (-2) * (a * Real.log (1 + (1 : ℝ) / b)) := by ring
      _ = (-2) * 1 := by rw [h1']
      _ = -2 := by ring
  have hlog_rel :
      Real.log (1 - (1 : ℝ) / b) = -2 * Real.log (1 + (1 : ℝ) / b) := by
    apply (mul_left_cancel₀ ha_ne)
    calc
      a * Real.log (1 - (1 : ℝ) / b) = -2 := hneg1'
      _ = a * (-2 * Real.log (1 + (1 : ℝ) / b)) := by
        symm
        exact hscaled
  have hlog_pow :
      Real.log ((1 + (1 : ℝ) / b) ^ (2 : ℝ)) =
        2 * Real.log (1 + (1 : ℝ) / b) := by
    exact Real.log_rpow hplus_pos (2 : ℝ)
  have hlog_sum :
      Real.log (1 - (1 : ℝ) / b) +
        Real.log ((1 + (1 : ℝ) / b) ^ (2 : ℝ)) = 0 := by
    linarith [hlog_rel, hlog_pow]
  have hpow_ne : ((1 + (1 : ℝ) / b) ^ (2 : ℝ)) ≠ 0 := by
    exact ne_of_gt (Real.rpow_pos_of_pos hplus_pos (2 : ℝ))
  have hlog_prod :
      Real.log ((1 - (1 : ℝ) / b) * ((1 + (1 : ℝ) / b) ^ (2 : ℝ))) = 0 := by
    calc
      Real.log ((1 - (1 : ℝ) / b) * ((1 + (1 : ℝ) / b) ^ (2 : ℝ)))
          = Real.log (1 - (1 : ℝ) / b) + Real.log ((1 + (1 : ℝ) / b) ^ (2 : ℝ)) := by
              simpa using (Real.log_mul hminus_ne hpow_ne)
      _ = 0 := hlog_sum
  have hprod_pos : 0 < (1 - (1 : ℝ) / b) * ((1 + (1 : ℝ) / b) ^ (2 : ℝ)) := by
    exact mul_pos hminus_pos (Real.rpow_pos_of_pos hplus_pos (2 : ℝ))
  have hprod_eq_one : (1 - (1 : ℝ) / b) * ((1 + (1 : ℝ) / b) ^ (2 : ℝ)) = 1 := by
    exact Real.eq_one_of_pos_of_log_eq_zero hprod_pos hlog_prod
  have hpoly : b ^ 2 - b - 1 = 0 := by
    have htmp : (1 - (1 : ℝ) / b) * (1 + (1 : ℝ) / b) ^ 2 = 1 := by
      simpa [Real.rpow_two] using hprod_eq_one
    field_simp [hb_ne] at htmp
    nlinarith [htmp]
  have hphi_poly : phi ^ 2 - phi - 1 = 0 := by
    linarith [phi_sq_eq]
  have hfactor : (b - phi) * (b + phi - 1) = 0 := by
    nlinarith [hpoly, hphi_poly]
  rcases mul_eq_zero.mp hfactor with hroot | hother
  · linarith
  · have hpos : 0 < b + phi - 1 := by
      linarith [hb, one_lt_phi]
    exact False.elim ((ne_of_gt hpos) hother)

/-- Under the three-point calibration, all affine-log parameters are forced. -/
theorem affine_log_parameters_forced_by_three_point_calibration
    {a b c : ℝ}
    (hb : 1 < b)
    (h0 : gapAffineLogR a b c 0 = 0)
    (h1 : gapAffineLogR a b c 1 = 1)
    (hneg1 : gapAffineLogR a b c (-1) = -2) :
    b = phi ∧ a = 1 / Real.log phi ∧ c = 0 := by
  have hbphi : b = phi := minus_one_step_forces_phi_shift hb h0 h1 hneg1
  have h0phi : gapAffineLogR a phi c 0 = 0 := by simpa [hbphi] using h0
  have h1phi : gapAffineLogR a phi c 1 = 1 := by simpa [hbphi] using h1
  have ha : a = 1 / Real.log phi := unit_step_forces_log_scale h0phi h1phi
  have hc : c = 0 := zero_normalization_forces_offset h0phi
  exact ⟨hbphi, ha, hc⟩

/-- Under the structural normalizations, the affine-log family is exactly the canonical gap. -/
theorem affine_log_collapses_to_canonical_gap
    {a c : ℝ}
    (h0 : gapAffineLogR a phi c 0 = 0)
    (h1 : gapAffineLogR a phi c 1 = 1) :
    ∀ Z : ℤ, gapAffineLog a phi c Z = RSBridge.gap Z := by
  have hc : c = 0 := zero_normalization_forces_offset h0
  have ha : a = 1 / Real.log phi := unit_step_forces_log_scale h0 h1
  intro Z
  unfold gapAffineLog gapAffineLogR RSBridge.gap
  calc
    a * Real.log (1 + (Z : ℝ) / phi) + c
        = (1 / Real.log phi) * Real.log (1 + (Z : ℝ) / phi) := by
            simp [ha, hc]
    _ = Real.log (1 + (Z : ℝ) / phi) / Real.log phi := by
          simp [div_eq_mul_inv, mul_comm]

/-- Three-point calibration gives direct collapse to the canonical RS gap on `ℤ`. -/
theorem affine_log_collapses_from_three_point_calibration
    {a b c : ℝ}
    (hb : 1 < b)
    (h0 : gapAffineLogR a b c 0 = 0)
    (h1 : gapAffineLogR a b c 1 = 1)
    (hneg1 : gapAffineLogR a b c (-1) = -2) :
    ∀ Z : ℤ, gapAffineLog a b c Z = RSBridge.gap Z := by
  have hbphi : b = phi := minus_one_step_forces_phi_shift hb h0 h1 hneg1
  have h0phi : gapAffineLogR a phi c 0 = 0 := by simpa [hbphi] using h0
  have h1phi : gapAffineLogR a phi c 1 = 1 := by simpa [hbphi] using h1
  intro Z
  simpa [hbphi] using affine_log_collapses_to_canonical_gap h0phi h1phi Z

/-- Uniqueness in the constrained affine-log class. -/
theorem affine_log_unique_under_normalizations
    {a₁ c₁ a₂ c₂ : ℝ}
    (h0₁ : gapAffineLogR a₁ phi c₁ 0 = 0)
    (h1₁ : gapAffineLogR a₁ phi c₁ 1 = 1)
    (h0₂ : gapAffineLogR a₂ phi c₂ 0 = 0)
    (h1₂ : gapAffineLogR a₂ phi c₂ 1 = 1) :
    ∀ Z : ℤ, gapAffineLog a₁ phi c₁ Z = gapAffineLog a₂ phi c₂ Z := by
  intro Z
  rw [affine_log_collapses_to_canonical_gap h0₁ h1₁ Z]
  rw [affine_log_collapses_to_canonical_gap h0₂ h1₂ Z]

/-- Compact certificate for the three-point affine-log forcing closure. -/
structure ThreePointAffineLogClosure (a b c : ℝ) where
  shift_forced : b = phi
  scale_forced : a = 1 / Real.log phi
  offset_forced : c = 0
  collapses_to_gap : ∀ Z : ℤ, gapAffineLog a b c Z = RSBridge.gap Z

/-- Build the closure certificate from three-point calibration data. -/
theorem three_point_affine_log_closure
    {a b c : ℝ}
    (hb : 1 < b)
    (h0 : gapAffineLogR a b c 0 = 0)
    (h1 : gapAffineLogR a b c 1 = 1)
    (hneg1 : gapAffineLogR a b c (-1) = -2) :
    ThreePointAffineLogClosure (a := a) (b := b) (c := c) := by
  have hparams : b = phi ∧ a = 1 / Real.log phi ∧ c = 0 :=
    affine_log_parameters_forced_by_three_point_calibration hb h0 h1 hneg1
  refine ⟨hparams.1, hparams.2.1, hparams.2.2, ?_⟩
  exact affine_log_collapses_from_three_point_calibration hb h0 h1 hneg1

end
end GapFunctionForcing
end Masses
end IndisputableMonolith

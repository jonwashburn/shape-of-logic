import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RSBridge.Anchor

/-!
# Gap Function Forcing (Three-Point Calibration)

Within the affine-log candidate family

  `g(x) = a · log(1 + x / b) + c`,

three normalization conditions uniquely fix all parameters:

1. `g(0) = 0` forces `c = 0`
2. `g(-1) = -2` with `b > 1` forces `b = φ`
3. `g(1) = 1` forces `a = 1 / log(φ)`

Together this collapses the family to the canonical gap function

  `gap(Z) = log(1 + Z/φ) / log(φ) = log_φ(1 + Z/φ)`.

## Scope of Uniqueness

The uniqueness proved here is within the affine-log family `a·log(1+x/b)+c`.
That this family is the correct bridge from multiplicative J-costs to additive
φ-ladder shifts is a structural postulate motivated by the logarithmic nature
of the cost-to-rung conversion, not a theorem derived from T0–T8.
-/

namespace IndisputableMonolith
namespace RSBridge
namespace GapFunctionForcing

open Real Constants

noncomputable section

/-- Affine-log candidate family on reals. -/
def gapAffineLogR (a b c x : ℝ) : ℝ :=
  a * Real.log (1 + x / b) + c

/-- Integer specialization. -/
def gapAffineLog (a b c : ℝ) (Z : ℤ) : ℝ :=
  gapAffineLogR a b c (Z : ℝ)

/-- `φ = 1 + 1/φ` (golden ratio identity). -/
lemma phi_eq_one_add_inv_phi : phi = 1 + (1 : ℝ) / phi := by
  have hne : phi ≠ 0 := phi_ne_zero
  calc
    phi = phi ^ 2 / phi := by field_simp [hne]
    _ = (phi + 1) / phi := by simp [phi_sq_eq]
    _ = 1 + (1 : ℝ) / phi := by field_simp [hne]

lemma one_add_inv_phi_eq_phi : 1 + (1 : ℝ) / phi = phi :=
  phi_eq_one_add_inv_phi.symm

lemma log_one_add_inv_phi_eq_log_phi : Real.log (1 + phi⁻¹) = Real.log phi := by
  have hshift : (1 + phi⁻¹ : ℝ) = phi := by
    simpa [one_div] using one_add_inv_phi_eq_phi
  simp [hshift]

/-! ## Step 1: g(0) = 0 forces c = 0 -/

lemma zero_normalization_forces_offset
    {a c : ℝ}
    (h0 : gapAffineLogR a phi c 0 = 0) :
    c = 0 := by
  simpa [gapAffineLogR] using h0

/-! ## Step 2: g(1) = 1 forces a = 1/log(φ) (given c = 0 and b = φ) -/

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

/-! ## Step 3: g(-1) = -2 forces b = φ (the key theorem)

This is the paper's Theorem 4.2: setting u = 1/b, the condition
`(1 - u)(1 + u)^2 = 1` expands to `u^2 + u - 1 = 0`, giving u = 1/φ. -/

theorem minus_one_step_forces_phi_shift
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
  have hminus_pos : 0 < 1 - (1 : ℝ) / b := by linarith
  have hminus_ne : (1 - (1 : ℝ) / b) ≠ 0 := ne_of_gt hminus_pos
  have hc : c = 0 := by simpa [gapAffineLogR] using h0
  have h1' : a * Real.log (1 + (1 : ℝ) / b) = 1 := by
    simpa [gapAffineLogR, hc] using h1
  have hneg1_raw : a * Real.log (1 + (-1 : ℝ) / b) = -2 := by
    simpa [gapAffineLogR, hc] using hneg1
  have hneg1' : a * Real.log (1 - (1 : ℝ) / b) = -2 := by
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc] using hneg1_raw
  have ha_ne : a ≠ 0 := by
    intro ha; simp [ha] at h1'
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
      _ = a * (-2 * Real.log (1 + (1 : ℝ) / b)) := hscaled.symm
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
  have hphi_poly : phi ^ 2 - phi - 1 = 0 := by linarith [phi_sq_eq]
  have hfactor : (b - phi) * (b + phi - 1) = 0 := by
    nlinarith [hpoly, hphi_poly]
  rcases mul_eq_zero.mp hfactor with hroot | hother
  · linarith
  · exact False.elim ((ne_of_gt (by linarith [hb, one_lt_phi] : 0 < b + phi - 1)) hother)

/-! ## Main Theorems -/

/-- Three-point calibration forces all affine-log parameters. -/
theorem affine_log_parameters_forced
    {a b c : ℝ}
    (hb : 1 < b)
    (h0 : gapAffineLogR a b c 0 = 0)
    (h1 : gapAffineLogR a b c 1 = 1)
    (hneg1 : gapAffineLogR a b c (-1) = -2) :
    b = phi ∧ a = 1 / Real.log phi ∧ c = 0 := by
  have hbphi : b = phi := minus_one_step_forces_phi_shift hb h0 h1 hneg1
  have h0phi : gapAffineLogR a phi c 0 = 0 := by simpa [hbphi] using h0
  have h1phi : gapAffineLogR a phi c 1 = 1 := by simpa [hbphi] using h1
  exact ⟨hbphi, unit_step_forces_log_scale h0phi h1phi,
         zero_normalization_forces_offset h0phi⟩

/-- Under the normalizations, the affine-log family equals the canonical gap. -/
theorem affine_log_collapses_to_gap
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

/-- Three-point calibration gives direct collapse to the canonical gap. -/
theorem three_point_forces_canonical_gap
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
  simpa [hbphi] using affine_log_collapses_to_gap h0phi h1phi Z

/-- Certificate structure for the three-point closure. -/
structure ThreePointClosure (a b c : ℝ) where
  shift_forced : b = phi
  scale_forced : a = 1 / Real.log phi
  offset_forced : c = 0
  collapses_to_gap : ∀ Z : ℤ, gapAffineLog a b c Z = RSBridge.gap Z

/-- Build the closure certificate from calibration data. -/
theorem three_point_closure
    {a b c : ℝ}
    (hb : 1 < b)
    (h0 : gapAffineLogR a b c 0 = 0)
    (h1 : gapAffineLogR a b c 1 = 1)
    (hneg1 : gapAffineLogR a b c (-1) = -2) :
    ThreePointClosure a b c := by
  have hparams := affine_log_parameters_forced hb h0 h1 hneg1
  exact ⟨hparams.1, hparams.2.1, hparams.2.2,
         three_point_forces_canonical_gap hb h0 h1 hneg1⟩

end
end GapFunctionForcing
end RSBridge
end IndisputableMonolith

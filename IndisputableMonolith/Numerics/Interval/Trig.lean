import IndisputableMonolith.Numerics.Interval.Basic
import IndisputableMonolith.Numerics.Interval.PiBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Interval Arithmetic for Trigonometric Functions

This module provides rigorous interval bounds for arctan and tan.

## Constructive proofs

All arctan bounds are proved constructively using derivative-comparison
monotonicity (`monotoneOn_of_deriv_nonneg`):

- For the **upper bound**: `arctan(x) ≤ x − x³/3 + x⁵/5`, because
  `(1−t²+t⁴) ≥ 1/(1+t²)` (equivalently `1+t⁶ ≥ 1`).

- For the **lower bound**: `x − x³/3 + x⁵/5 − x⁷/7 ≤ arctan(x)`, because
  `(1−t²+t⁴−t⁶) ≤ 1/(1+t²)` (equivalently `1−t⁸ ≤ 1`).

Both polynomials are antiderivatives of their respective bounding functions,
and the comparison follows from `monotoneOn_of_deriv_nonneg` on `[0,∞)`.

The arctan(2) identity `arctan(2) = π/4 + arctan(1/3)` is proved using
`Real.arctan_add` from Mathlib.
-/

namespace IndisputableMonolith.Numerics

open Interval
open Real
open Filter
open scoped Topology Finset

/-! ## §1. Taylor-polynomial bounds for arctan via derivative comparison -/

/-- Upper bounding polynomial: g(x) = x − x³/3 + x⁵/5 -/
private noncomputable def g_upper (x : ℝ) : ℝ := x - x ^ 3 / 3 + x ^ 5 / 5

private theorem g_upper_continuous : Continuous g_upper := by unfold g_upper; fun_prop
private theorem g_upper_differentiable : Differentiable ℝ g_upper := by unfold g_upper; fun_prop

private theorem g_upper_deriv (t : ℝ) :
    HasDerivAt g_upper (1 - t ^ 2 + t ^ 4) t := by
  unfold g_upper
  have := ((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)).add
    ((hasDerivAt_pow 5 t).div_const 5)
  convert this using 1; ring

/-- Key inequality: `1/(1+t²) ≤ 1 − t² + t⁴` for all t.
    Proof: `(1−t²+t⁴)(1+t²) = 1+t⁶ ≥ 1`. -/
private theorem inv_one_add_sq_le_upper (t : ℝ) :
    1 / (1 + t ^ 2) ≤ 1 - t ^ 2 + t ^ 4 := by
  rw [div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  have : (1 - t ^ 2 + t ^ 4) * (1 + t ^ 2) = 1 + t ^ 6 := by ring
  rw [this]; linarith [sq_nonneg (t ^ 3)]

/-- `arctan(x) ≤ x − x³/3 + x⁵/5` for x ≥ 0. -/
theorem arctan_le_upper_poly (x : ℝ) (hx : 0 ≤ x) : arctan x ≤ g_upper x := by
  suffices h : 0 ≤ g_upper x - arctan x by linarith
  have hkey : MonotoneOn (fun t => g_upper t - arctan t) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((g_upper_continuous.sub continuous_arctan).continuousOn)
      (fun t _ => ((g_upper_differentiable t).sub
        (hasDerivAt_arctan t).differentiableAt).differentiableWithinAt)
      (fun t ht => by
        simp only [Set.nonempty_Iio, interior_Ici'] at ht
        have hd : HasDerivAt (fun s => g_upper s - arctan s)
          ((1 - t^2 + t^4) - 1/(1+t^2)) t :=
          (g_upper_deriv t).sub (hasDerivAt_arctan t)
        rw [hd.deriv]
        linarith [inv_one_add_sq_le_upper t])
  linarith [hkey (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx) hx,
            show g_upper 0 - arctan 0 = 0 by simp [g_upper, arctan_zero]]

/-- Lower bounding polynomial: h(x) = x − x³/3 + x⁵/5 − x⁷/7 -/
private noncomputable def h_lower (x : ℝ) : ℝ := x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7

private theorem h_lower_continuous : Continuous h_lower := by unfold h_lower; fun_prop
private theorem h_lower_differentiable : Differentiable ℝ h_lower := by unfold h_lower; fun_prop

private theorem h_lower_deriv (t : ℝ) :
    HasDerivAt h_lower (1 - t ^ 2 + t ^ 4 - t ^ 6) t := by
  unfold h_lower
  have := (((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 3)).add
    ((hasDerivAt_pow 5 t).div_const 5)).sub ((hasDerivAt_pow 7 t).div_const 7)
  convert this using 1; ring

/-- Key inequality: `1 − t² + t⁴ − t⁶ ≤ 1/(1+t²)` for all t.
    Proof: `(1−t²+t⁴−t⁶)(1+t²) = 1−t⁸ ≤ 1`. -/
private theorem lower_le_inv_one_add_sq (t : ℝ) :
    1 - t ^ 2 + t ^ 4 - t ^ 6 ≤ 1 / (1 + t ^ 2) := by
  rw [le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)]
  have : (1 - t ^ 2 + t ^ 4 - t ^ 6) * (1 + t ^ 2) = 1 - t ^ 8 := by ring
  rw [this]; linarith [sq_nonneg (t ^ 4)]

/-- `x − x³/3 + x⁵/5 − x⁷/7 ≤ arctan(x)` for x ≥ 0. -/
theorem lower_poly_le_arctan (x : ℝ) (hx : 0 ≤ x) : h_lower x ≤ arctan x := by
  suffices h : 0 ≤ arctan x - h_lower x by linarith
  have hkey : MonotoneOn (fun t => arctan t - h_lower t) (Set.Ici 0) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      ((continuous_arctan.sub h_lower_continuous).continuousOn)
      (fun t _ => ((hasDerivAt_arctan t).differentiableAt.sub
        (h_lower_differentiable t)).differentiableWithinAt)
      (fun t ht => by
        simp only [Set.nonempty_Iio, interior_Ici'] at ht
        have hd : HasDerivAt (fun s => arctan s - h_lower s)
          (1/(1+t^2) - (1 - t^2 + t^4 - t^6)) t :=
          (hasDerivAt_arctan t).sub (h_lower_deriv t)
        rw [hd.deriv]
        linarith [lower_le_inv_one_add_sq t])
  linarith [hkey (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx) hx,
            show arctan 0 - h_lower 0 = 0 by simp [h_lower, arctan_zero]]

/-! ## §2. Constructive arctan(1/3) interval -/

/-- Interval containing arctan(1/3) ≈ 0.32175 -/
def arctanOneThirdInterval : Interval where
  lo := 321 / 1000  -- 0.321
  hi := 322 / 1000  -- 0.322
  valid := by norm_num

/-- **PROVED**: arctan(1/3) is in arctanOneThirdInterval.
    Lower bound from `h_lower(1/3) = 24628/76545 ≥ 321/1000`.
    Upper bound from `g_upper(1/3) = 391/1215 ≤ 322/1000`. -/
theorem arctan_one_third_in_interval :
    arctanOneThirdInterval.contains (arctan (1 / 3)) := by
  simp only [contains, arctanOneThirdInterval]
  constructor
  · -- lower: ↑(321/1000 : ℚ) ≤ arctan(1/3)
    have hlo := lower_poly_le_arctan (1 / 3) (by norm_num)
    have hval : h_lower (1 / 3) = 24628 / 76545 := by unfold h_lower; norm_num
    rw [hval] at hlo
    have hq : ((321 / 1000 : ℚ) : ℝ) ≤ (24628 : ℝ) / 76545 := by push_cast; norm_num
    linarith
  · -- upper: arctan(1/3) ≤ ↑(322/1000 : ℚ)
    have hhi := arctan_le_upper_poly (1 / 3) (by norm_num)
    have hval : g_upper (1 / 3) = 391 / 1215 := by unfold g_upper; norm_num
    rw [hval] at hhi
    have hq : (391 : ℝ) / 1215 ≤ ((322 / 1000 : ℚ) : ℝ) := by push_cast; norm_num
    linarith

/-! ## §3. Constructive arctan(2) interval via addition formula -/

/-- **PROVED**: `arctan(2) = π/4 + arctan(1/3)`.
    From the addition formula: `arctan(1) + arctan(1/3) = arctan(2)`. -/
theorem arctan_two_eq : arctan 2 = Real.pi / 4 + arctan (1 / 3) := by
  have h1 : arctan 1 = Real.pi / 4 := by
    rw [← tan_pi_div_four]
    exact arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])
  have hadd : arctan 1 + arctan (1 / 3) = arctan 2 := by
    rw [arctan_add (by norm_num : (1 : ℝ) * (1 / 3) < 1)]
    congr 1; norm_num
  linarith

/-- Interval containing arctan 2 = π/4 + arctan(1/3) -/
def arctanTwoInterval : Interval :=
  let pi4 := smulPos (1 / 4) piInterval (by norm_num)
  add pi4 arctanOneThirdInterval

/-- **PROVED**: arctan(2) is in arctanTwoInterval. -/
theorem arctan_two_in_interval :
    arctanTwoInterval.contains (arctan 2) := by
  rw [arctan_two_eq]
  unfold arctanTwoInterval
  apply add_contains_add
  · -- π/4 is in (1/4) · piInterval
    have hpi := pi_in_piInterval
    have := smulPos_contains_smul (q := 1 / 4) (by norm_num : (0 : ℚ) < 1 / 4) hpi
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at this
    convert this using 1
    ring
  · exact arctan_one_third_in_interval

end IndisputableMonolith.Numerics

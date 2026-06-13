import Mathlib

/-!
# Gravity: Parameterization Bridge (Acceleration ↔ Dynamical Time)

This module formalizes the exact algebraic identities that relate:
- circular-orbit acceleration \(a = v^2/r\),
- orbital/dynamical time \(T_{\rm dyn} = 2\pi r/v\),
and the common "characteristic time" \(T_0 = 2\pi\sqrt{r_0/a_0}\).

These identities are the precise bridge underlying the relationship between
"acceleration-parameterized" and "time-parameterized" weight forms.

## Status

All bridge identities and exponent-mapping theorems in this module are fully proven
(no `sorry`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace ParameterizationBridge

open Real

noncomputable section

/-- Circular-orbit centripetal acceleration from speed `v` and radius `r`. -/
def accel (v r : ℝ) : ℝ := v^2 / r

/-- Orbital (dynamical) time for circular motion (one full revolution). -/
def Tdyn (v r : ℝ) : ℝ := 2 * Real.pi * r / v

/-- Characteristic dynamical time constructed from a length scale `r0` and acceleration scale `a0`:
\[
T_0 = 2\pi\sqrt{r_0/a_0}.
\]
-/
def T0 (r0 a0 : ℝ) : ℝ := 2 * Real.pi * Real.sqrt (r0 / a0)

/-- Core identity: \(a\,T_{\rm dyn}^2 = 4\pi^2 r\). -/
theorem accel_mul_Tdyn_sq (v r : ℝ) (hv : v ≠ 0) (hr : r ≠ 0) :
    accel v r * (Tdyn v r)^2 = 4 * (Real.pi ^ 2) * r := by
  unfold accel Tdyn
  field_simp [hv, hr]
  ring

/-- Square of the characteristic time: \(T_0^2 = 4\pi^2 (r_0/a_0)\). -/
theorem T0_sq (r0 a0 : ℝ) (hr0 : 0 ≤ r0) (ha0 : 0 < a0) :
    (T0 r0 a0)^2 = 4 * (Real.pi ^ 2) * (r0 / a0) := by
  unfold T0
  have hnonneg : 0 ≤ r0 / a0 := div_nonneg hr0 (le_of_lt ha0)
  have hsq : Real.sqrt (r0 / a0) ^ 2 = r0 / a0 := Real.sq_sqrt hnonneg
  calc (2 * Real.pi * Real.sqrt (r0 / a0))^2
      = (2 * Real.pi)^2 * (Real.sqrt (r0 / a0))^2 := by ring
    _ = 4 * Real.pi^2 * (r0 / a0) := by rw [hsq]; ring

/-- **Bridge identity (exact):**
\[
\left(\frac{T_{\rm dyn}}{T_0}\right)^2 = \left(\frac{a_0}{a}\right)\left(\frac{r}{r_0}\right)
\]
for circular motion with \(a=v^2/r\) and \(T_{\rm dyn}=2\pi r/v\).

This is the fundamental kinematic identity underlying the acceleration↔time parameterization.
-/
theorem time_ratio_sq_eq_accel_ratio_mul_r_ratio
    (v r a0 r0 : ℝ) (hv : 0 < v) (hr : 0 < r) (ha0 : 0 < a0) (hr0 : 0 < r0) :
    let a := accel v r
    let T := Tdyn v r
    let Tref := T0 r0 a0
    (T / Tref)^2 = (a0 / a) * (r / r0) := by
  -- Direct algebraic verification
  intro a T Tref
  dsimp [a, T, Tref]
  have hv0 : v ≠ 0 := ne_of_gt hv
  have hr0' : r ≠ 0 := ne_of_gt hr
  have ha0_ne : a0 ≠ 0 := ne_of_gt ha0
  have hr0_ne : r0 ≠ 0 := ne_of_gt hr0

  have ha : accel v r ≠ 0 := by
    unfold accel
    exact div_ne_zero (pow_ne_zero 2 hv0) hr0'

  -- Expand the square of a ratio as a ratio of squares.
  rw [div_pow (Tdyn v r) (T0 r0 a0) 2]

  -- Use the pre-proved square identities for `Tdyn` and `T0`.
  have hT_sq : (Tdyn v r)^2 = (4 * (Real.pi ^ 2) * r) / accel v r := by
    have h := accel_mul_Tdyn_sq (v := v) (r := r) hv0 hr0'
    apply (eq_div_iff ha).2
    -- Commute multiplication to match the target.
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

  have hT0_sq : (T0 r0 a0)^2 = 4 * (Real.pi ^ 2) * (r0 / a0) :=
    T0_sq r0 a0 (le_of_lt hr0) ha0

  rw [hT_sq, hT0_sq]
  -- Clear denominators and finish by ring normalization.
  field_simp [ha, ha0_ne, hr0_ne]

/-- Rearranged bridge:
\[
\frac{a_0}{a} = \left(\frac{T_{\rm dyn}}{T_0}\right)^2\left(\frac{r_0}{r}\right).
\]
-/
theorem accel_ratio_eq_time_ratio_sq_mul_r0_over_r
    (v r a0 r0 : ℝ) (hv : 0 < v) (hr : 0 < r) (ha0 : 0 < a0) (hr0 : 0 < r0) :
    let a := accel v r
    let T := Tdyn v r
    let Tref := T0 r0 a0
    (a0 / a) = (T / Tref)^2 * (r0 / r) := by
  -- Algebraic rearrangement of time_ratio_sq_eq_accel_ratio_mul_r_ratio
  intro a T Tref
  have hbridge :
      (T / Tref)^2 = (a0 / a) * (r / r0) := by
    simpa [a, T, Tref] using
      time_ratio_sq_eq_accel_ratio_mul_r_ratio (v := v) (r := r) (a0 := a0) (r0 := r0) hv hr ha0 hr0

  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hr0_ne : r0 ≠ 0 := ne_of_gt hr0

  have hcancel : (r / r0) * (r0 / r) = (1 : ℝ) := by
    field_simp [hr_ne, hr0_ne]

  -- Multiply both sides of the bridge by `r0/r` and simplify.
  have hmul := congrArg (fun x => x * (r0 / r)) hbridge
  have : (T / Tref)^2 * (r0 / r) = a0 / a := by
    -- Reassociate and cancel `(r/r0) * (r0/r) = 1`.
    simpa [mul_assoc, hcancel] using hmul

  exact this.symm

/-- **Exponent bridge (canonical special case):** at the characteristic radius \(r=r_0\),
\[
\left(\frac{a_0}{a}\right)^\alpha = \left(\frac{T_{\rm dyn}}{T_0}\right)^{2\alpha}.
\]

This is the exact statement behind the common "acceleration exponent vs time exponent" mapping:
if a model is written with \((a_0/a)^{\alpha_{\rm acc}}\), the corresponding exponent on
the time-ratio base is \(2\alpha_{\rm acc}\) (at \(r=r_0\)).
-/
theorem accel_power_eq_time_power_at_r_eq_r0
    (v r0 a0 α : ℝ) (hv : 0 < v) (hr0 : 0 < r0) (ha0 : 0 < a0) :
    let a := accel v r0
    let T := Tdyn v r0
    let Tref := T0 r0 a0
    (a0 / a) ^ α = (T / Tref) ^ ((2 : ℝ) * α) := by
  intro a T Tref
  -- At r = r0, from the bridge: (T/Tref)^2 = a0/a
  -- Thus (a0/a)^α = ((T/Tref)^2)^α = (T/Tref)^(2α)
  have h : (T / Tref)^2 = a0 / a := by
    have hbridge := time_ratio_sq_eq_accel_ratio_mul_r_ratio v r0 a0 r0 hv hr0 ha0 hr0
    have hr00 : r0 ≠ 0 := ne_of_gt hr0
    simp only [div_self hr00, mul_one] at hbridge
    exact hbridge
  rw [← h]
  have hT_pos : 0 < T := by
    unfold T Tdyn
    have h2pi : 0 < (2 : ℝ) * Real.pi := by nlinarith [Real.pi_pos]
    exact div_pos (mul_pos h2pi hr0) hv
  have hTref_pos : 0 < Tref := by
    unfold Tref T0
    have hpos : 0 < r0 / a0 := div_pos hr0 ha0
    have hsqrt : 0 < Real.sqrt (r0 / a0) := Real.sqrt_pos.mpr hpos
    have h2pi : 0 < (2 : ℝ) * Real.pi := by nlinarith [Real.pi_pos]
    exact mul_pos h2pi hsqrt
  have hratio_pos : 0 < T / Tref := div_pos hT_pos hTref_pos
  have hratio_nonneg : 0 ≤ T / Tref := le_of_lt hratio_pos
  -- ((T/Tref)^2)^α = (T/Tref)^(2*α)
  rw [← Real.rpow_natCast (T / Tref) 2]
  rw [← Real.rpow_mul hratio_nonneg]
  norm_cast

/-- **Exponent bridge (time→acceleration form):** at the characteristic radius \(r=r_0\),
\[
\left(\frac{T_{\rm dyn}}{T_0}\right)^{\alpha}
= \left(\frac{a_0}{a}\right)^{\alpha/2}.
\]

This is the exact mapping when the exponent \(\alpha\) is interpreted as the
**time-exponent** (as in a time-kernel), and one rewrites the model in acceleration space.
-/
theorem time_power_eq_accel_power_at_r_eq_r0
    (v r0 a0 α : ℝ) (hv : 0 < v) (hr0 : 0 < r0) (ha0 : 0 < a0) :
    let a := accel v r0
    let T := Tdyn v r0
    let Tref := T0 r0 a0
    (T / Tref) ^ α = (a0 / a) ^ (α / 2) := by
  intro a T Tref
  -- Use the already-proved form with exponent α/2
  have h := accel_power_eq_time_power_at_r_eq_r0 v r0 a0 (α / 2) hv hr0 ha0
  -- h: (a0/a)^(α/2) = (T/Tref)^(2*(α/2)) = (T/Tref)^α
  have : 2 * (α / 2) = α := by ring
  simp only [this] at h
  exact h.symm

end
end ParameterizationBridge
end Gravity
end IndisputableMonolith

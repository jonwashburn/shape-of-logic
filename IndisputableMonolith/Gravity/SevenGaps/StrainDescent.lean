import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.HingeStationarityCore

/-!
# The strain descent: a convergent least-cost flow on the link

## Why this module exists

The C2 bridge's last premise with physical content is the existence half of
its stationarity adoption: the substrate attains the sourced least-cost
carrier on each hinge's link. The descent wall
(`Foundation.RecognitionUpdateDescentWall`) proves the canonical tick update
cannot carry that premise: on its eventual image the update is 8-periodic,
so no functional it descends is non-constant there. The premise needs a new
object: a dynamics on the carrier's strain space. This module builds it and
proves it convergent.

## The construction

The sourced action on a link decomposes per channel
(`sourcedAction_eq_sum`): `Φ_c(t) = Σ_i (cosh t_i - 1) - (c/n) Σ_i t_i`.
The per-channel cost is `ψ_a(s) = cosh s - 1 - a·s` with `a = c/n`,
strictly convex with unique stationary point `s* = arsinh a`. The descent is
the gradient step with an explicit self-tuned step size. Writing `g :=
sinh s - a` (the residual),

  `E := max (2·(cosh s / 2 + |sinh s|·|g|/6)·cosh |g|) (cosh (|s|+|g|))`,
  `η := E⁻¹`,   `s' := s - η·g`,

the envelope is chosen so that the Lyapunov bound and the contraction bound
hold at once.

## What is proved (all THEOREM; 0 sorry, 0 admit, no new axiom, no
`native_decide`)

* Scalar bounds from single integrals: `cosh x - 1 ≤ (x²/2)·cosh x`
  (`cosh_sub_one_le_sq_half_cosh`) and `|sinh x - x| ≤ (|x|³/6)·cosh x`
  (`abs_sinh_sub_self_le_sixth`), by FTC plus monotonicity of cosh on `ℝ≥0`
  (`cosh_le_cosh_of_nonneg_of_le`, an elementary exponential proof).
* `step_one_dim_sub`: the exact algebraic identity of one step (cosh/sinh
  addition laws, no Taylor theorem).
* `descent_one_dim`: the Lyapunov decrease `ψ(s') - ψ(s) ≤ -(η/2)·g²`.
* `descent_one_dim_lt` / `step_fixed_iff_arsinh`: strict decrease exactly
  off the stationary point; the step's fixed points are exactly
  `s* = arsinh a` (via `Real.sinh_injective`).
* `contraction_one_dim`: `|s' - s*| ≤ (1 - η)·|s - s*|` with `η > 0`, from
  the mean value theorem for `sinh`.
* `strainOrbit_abs_le` and `strainOrbit_tendsto`: the iterated step
  converges geometrically to `arsinh a` with a uniform explicit rate on the
  initial level set, hence `Tendsto (strainOrbit a s₀) atTop (𝓝 s*)`.
* Vector forms on the link: `strainStepVec` (componentwise), the sourced
  action strictly decreases off the minimizer (`sourcedAction_step_lt`),
  the fixed points are exactly `sourcedMinimizer n c`
  (`stepVec_fixed_iff_minimizer`), and each channel converges
  (`strainStepVec_tendsto_minimizer`).

## The honest verdict for (A3)

The flow is the steepest descent of the FORCED cost: the descent direction
`sinh t_i - c/n` is the derivative of the ledger's own cost in the log
coordinate, i.e. the recognition phase `ph(e^{t_i})` itself (banked:
`d/dt J(e^t) = ph(e^t)`). The flow is orientation-free: its only signed
input is the adopted source `c`. So the stationarity premise is reduced to
one named dynamical principle: that the substrate's strain state follows
the steepest descent of its total recognition cost. Whether THAT principle
is itself derivable from the recognition kernel (rather than adopted) is
the remaining open question, named in the record.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace StrainDescent

open Real Set Filter
open scoped Topology

noncomputable section

/-! ## §1. The one-dimensional objects and the scalar bounds -/

/-- The per-channel sourced cost: `ψ_a(s) = cosh s - 1 - a·s`. -/
def sourceCost1 (a : ℝ) : ℝ → ℝ := fun s => Real.cosh s - 1 - a * s

/-- The residual (the gradient of the per-channel cost): `sinh s - a`. -/
def strainResidual (a : ℝ) : ℝ → ℝ := fun s => Real.sinh s - a

/-- The envelope: the larger of the two bounds the proof needs,
`2·(cosh s / 2 + |sinh s|·|g|/6)·cosh |g|` for the Lyapunov assembly and
`cosh (|s|+|g|)` for the contraction. -/
def strainEnvelope (a s : ℝ) : ℝ :=
  max (2 * (Real.cosh s / 2 + |Real.sinh s| * |strainResidual a s| / 6)
      * Real.cosh (|strainResidual a s|))
    (Real.cosh (|s| + |strainResidual a s|))

/-- The self-tuned step size: the reciprocal of the envelope. -/
def strainStepSize (a s : ℝ) : ℝ := (strainEnvelope a s)⁻¹

/-- One descent step: `s' = s - η·g`. -/
def strainStep1 (a s : ℝ) : ℝ := s - strainStepSize a s * strainResidual a s

/-- The envelope is at least `1`. -/
theorem strainEnvelope_ge_one (a s : ℝ) : 1 ≤ strainEnvelope a s := by
  unfold strainEnvelope
  exact le_max_of_le_right (Real.one_le_cosh _)

/-- The envelope is strictly positive. -/
theorem strainEnvelope_pos (a s : ℝ) : 0 < strainEnvelope a s :=
  lt_of_lt_of_le one_pos (strainEnvelope_ge_one a s)

/-- The step size is strictly positive. -/
theorem strainStepSize_pos (a s : ℝ) : 0 < strainStepSize a s := by
  unfold strainStepSize
  exact inv_pos.mpr (strainEnvelope_pos a s)

/-- The step size is at most `1`. -/
theorem strainStepSize_le_one (a s : ℝ) : strainStepSize a s ≤ 1 := by
  unfold strainStepSize
  rw [inv_le_one_iff₀]
  exact Or.inr (strainEnvelope_ge_one a s)

/-- `cosh` is monotone on `ℝ≥0`: for `0 ≤ t ≤ x`, `cosh t ≤ cosh x`.
The difference factors as `(e^x - e^t)(1 - e^{-(x+t)})/2 ≥ 0`. -/
theorem cosh_le_cosh_of_nonneg_of_le {t x : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) :
    Real.cosh t ≤ Real.cosh x := by
  have hx : 0 ≤ x := le_trans ht htx
  have key : Real.cosh x - Real.cosh t
      = (Real.exp x - Real.exp t) * (1 - Real.exp (-x) * Real.exp (-t)) / 2 := by
    rw [Real.cosh_eq, Real.cosh_eq, Real.exp_neg, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  have h1 : (0:ℝ) ≤ Real.exp x - Real.exp t := sub_nonneg.mpr (Real.exp_le_exp.mpr htx)
  have h2 : Real.exp (-x) * Real.exp (-t) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have h3 : (0:ℝ) ≤ 1 - Real.exp (-x) * Real.exp (-t) := sub_nonneg.mpr h2
  have h4 : (0:ℝ) ≤ (Real.exp x - Real.exp t) * (1 - Real.exp (-x) * Real.exp (-t)) / 2 :=
    div_nonneg (mul_nonneg h1 h3) (by norm_num)
  linarith [key, h4]

/-- The FTC evaluations for cosh and sinh, stated for all `x` (oriented). -/
theorem integral_sinh (x : ℝ) :
    ∫ t in (0:ℝ)..x, Real.sinh t = Real.cosh x - 1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := Real.cosh) (f' := Real.sinh) (a := 0) (b := x)
    (fun t _ => Real.hasDerivAt_cosh t)
    (Real.continuous_sinh.intervalIntegrable _ _)
  simpa using h

theorem integral_cosh (x : ℝ) :
    ∫ t in (0:ℝ)..x, Real.cosh t = Real.sinh x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := Real.sinh) (f' := Real.cosh) (a := 0) (b := x)
    (fun t _ => Real.hasDerivAt_sinh t)
    (Real.continuous_cosh.intervalIntegrable _ _)
  simpa using h

/-- For `t ≥ 0`: `sinh t ≤ t · cosh t`. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ t * Real.cosh t := by
  rw [← integral_cosh t]
  calc ∫ u in (0:ℝ)..t, Real.cosh u
      ≤ ∫ u in (0:ℝ)..t, Real.cosh t :=
        intervalIntegral.integral_mono_on ht
          (Real.continuous_cosh.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
          (fun u hu => cosh_le_cosh_of_nonneg_of_le hu.1 hu.2)
    _ = t * Real.cosh t := by
        rw [intervalIntegral.integral_const]
        simp [mul_comm]

/-- The antiderivative of `t ↦ t` on `[0, x]`. -/
theorem integral_id_half_sq (x : ℝ) :
    ∫ t in (0:ℝ)..x, (t : ℝ) = x ^ 2 / 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t ^ 2 / 2) (f' := fun t : ℝ => t)
    (a := 0) (b := x)
    (fun t _ => by
      have hder := ((hasDerivAt_id t).pow 2).div_const 2
      convert hder using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring)
    (continuous_id.intervalIntegrable _ _)
  simpa using h

/-- The antiderivative of `t ↦ t²/2` on `[0, x]`. -/
theorem integral_sq_half_third (x : ℝ) :
    ∫ t in (0:ℝ)..x, (t ^ 2 / 2 : ℝ) = x ^ 3 / 6 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => t ^ 3 / 6) (f' := fun t : ℝ => t ^ 2 / 2)
    (a := 0) (b := x)
    (fun t _ => by
      have hder := ((hasDerivAt_id t).pow 3).div_const 6
      convert hder using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring)
    (((continuous_id.pow 2).div_const 2).intervalIntegrable _ _)
  simpa using h

/-- **First scalar bound**: `cosh x - 1 ≤ (x²/2)·cosh x`, all `x`. -/
theorem cosh_sub_one_le_sq_half_cosh (x : ℝ) :
    Real.cosh x - 1 ≤ (x ^ 2 / 2) * Real.cosh x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [← integral_sinh x]
    calc ∫ t in (0:ℝ)..x, Real.sinh t
        ≤ ∫ t in (0:ℝ)..x, (fun t => t * Real.cosh x) t := by
          apply intervalIntegral.integral_mono_on hx
            (Real.continuous_sinh.intervalIntegrable _ _)
            ((continuous_id.mul continuous_const).intervalIntegrable _ _)
          · intro t ht'
            exact le_trans (sinh_le_mul_cosh ht'.1)
              (mul_le_mul_of_nonneg_left
                (cosh_le_cosh_of_nonneg_of_le ht'.1 ht'.2) ht'.1)
      _ = (x ^ 2 / 2) * Real.cosh x := by
          rw [intervalIntegral.integral_mul_const, integral_id_half_sq]
  · have h0 : 0 ≤ -x := le_of_lt (neg_pos.mpr hx)
    have hmain : Real.cosh (-x) - 1 ≤ ((-x) ^ 2 / 2) * Real.cosh (-x) := by
      rw [← integral_sinh (-x)]
      calc ∫ t in (0:ℝ)..(-x), Real.sinh t
          ≤ ∫ t in (0:ℝ)..(-x), (fun t => t * Real.cosh (-x)) t := by
            apply intervalIntegral.integral_mono_on h0
              (Real.continuous_sinh.intervalIntegrable _ _)
              ((continuous_id.mul continuous_const).intervalIntegrable _ _)
            · intro t ht'
              exact le_trans (sinh_le_mul_cosh ht'.1)
                (mul_le_mul_of_nonneg_left
                  (cosh_le_cosh_of_nonneg_of_le ht'.1 ht'.2) ht'.1)
        _ = ((-x) ^ 2 / 2) * Real.cosh (-x) := by
            rw [intervalIntegral.integral_mul_const, integral_id_half_sq]
    rwa [Real.cosh_neg, neg_sq] at hmain

/-- **Second scalar bound**: `|sinh x - x| ≤ (|x|³/6)·cosh x`, all `x`. -/
theorem abs_sinh_sub_self_le_sixth (x : ℝ) :
    |Real.sinh x - x| ≤ (|x| ^ 3 / 6) * Real.cosh x := by
  rcases le_or_gt 0 x with hx | hx
  · have hnonneg : (0:ℝ) ≤ Real.sinh x - x := by
      rw [show Real.sinh x - x = ∫ t in (0:ℝ)..x, (Real.cosh t - 1) from
        by rw [intervalIntegral.integral_sub
            (Real.continuous_cosh.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _),
            integral_cosh, intervalIntegral.integral_const]; simp]
      apply intervalIntegral.integral_nonneg hx
      intro t _
      have h1 : (1:ℝ) ≤ Real.cosh t := Real.one_le_cosh t
      simp [h1]
    rw [abs_of_nonneg hnonneg, abs_of_nonneg hx]
    calc Real.sinh x - x
        = ∫ t in (0:ℝ)..x, (Real.cosh t - 1) := by
          rw [intervalIntegral.integral_sub
            (Real.continuous_cosh.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _),
            integral_cosh, intervalIntegral.integral_const]
          simp
      _ ≤ ∫ t in (0:ℝ)..x, (fun t => (t ^ 2 / 2) * Real.cosh x) t := by
          apply intervalIntegral.integral_mono_on hx
            ((Real.continuous_cosh.sub continuous_const).intervalIntegrable _ _)
            (((continuous_id.pow 2).div_const 2).mul continuous_const
              |>.intervalIntegrable _ _)
          · intro t ht'
            have h1 : Real.cosh t - 1 ≤ (t ^ 2 / 2) * Real.cosh t :=
              cosh_sub_one_le_sq_half_cosh t
            have h2 : Real.cosh t ≤ Real.cosh x :=
              cosh_le_cosh_of_nonneg_of_le ht'.1 ht'.2
            exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = (x ^ 3 / 6) * Real.cosh x := by
          rw [intervalIntegral.integral_mul_const, integral_sq_half_third]
  · have h0 : 0 ≤ -x := le_of_lt (neg_pos.mpr hx)
    have hodd : Real.sinh x - x = -(Real.sinh (-x) - (-x)) := by
      rw [Real.sinh_neg]; ring
    have hmain : |Real.sinh (-x) - (-x)| ≤ ((-x) ^ 3 / 6) * Real.cosh (-x) := by
      have hnonneg : (0:ℝ) ≤ Real.sinh (-x) - (-x) := by
        rw [show Real.sinh (-x) - (-x)
            = ∫ t in (0:ℝ)..(-x), (Real.cosh t - 1) from
          by rw [intervalIntegral.integral_sub
              (Real.continuous_cosh.intervalIntegrable _ _)
              (continuous_const.intervalIntegrable _ _),
              integral_cosh, intervalIntegral.integral_const]; simp]
        apply intervalIntegral.integral_nonneg h0
        intro t _
        have h1 : (1:ℝ) ≤ Real.cosh t := Real.one_le_cosh t
        simp [h1]
      rw [abs_of_nonneg hnonneg]
      calc Real.sinh (-x) - (-x)
          = ∫ t in (0:ℝ)..(-x), (Real.cosh t - 1) := by
            rw [intervalIntegral.integral_sub
              (Real.continuous_cosh.intervalIntegrable _ _)
              (continuous_const.intervalIntegrable _ _),
              integral_cosh, intervalIntegral.integral_const]
            simp
        _ ≤ ∫ t in (0:ℝ)..(-x), (fun t => (t ^ 2 / 2) * Real.cosh (-x)) t := by
            apply intervalIntegral.integral_mono_on h0
              ((Real.continuous_cosh.sub continuous_const).intervalIntegrable _ _)
              (((continuous_id.pow 2).div_const 2).mul continuous_const
                |>.intervalIntegrable _ _)
            · intro t ht'
              have h1 : Real.cosh t - 1 ≤ (t ^ 2 / 2) * Real.cosh t :=
                cosh_sub_one_le_sq_half_cosh t
              have h2 : Real.cosh t ≤ Real.cosh (-x) :=
                cosh_le_cosh_of_nonneg_of_le ht'.1 ht'.2
              exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
        _ = ((-x) ^ 3 / 6) * Real.cosh (-x) := by
            rw [intervalIntegral.integral_mul_const, integral_sq_half_third]
    calc |Real.sinh x - x|
        = |-(Real.sinh (-x) - (-x))| := by rw [hodd]
      _ = |Real.sinh (-x) - (-x)| := abs_neg _
      _ ≤ ((-x) ^ 3 / 6) * Real.cosh (-x) := hmain
      _ = (|x| ^ 3 / 6) * Real.cosh x := by
          rw [Real.cosh_neg, abs_of_neg hx, neg_pow]

/-! ## §2. The exact one-step identity and the Lyapunov decrease -/

/-- **The exact identity for one step** (no Taylor theorem). -/
theorem step_one_dim_sub (a s : ℝ) :
    sourceCost1 a (strainStep1 a s) - sourceCost1 a s
      = - strainStepSize a s * strainResidual a s ^ 2
        + Real.cosh s * (Real.cosh (strainStepSize a s * strainResidual a s) - 1)
        - Real.sinh s * (Real.sinh (strainStepSize a s * strainResidual a s)
            - strainStepSize a s * strainResidual a s) := by
  unfold sourceCost1 strainStep1 strainResidual
  rw [Real.cosh_sub]
  ring

/-- The cosh-on-the-step is bounded by the cosh of the residual. -/
theorem cosh_step_le_cosh_abs_residual (a s : ℝ) :
    Real.cosh (strainStepSize a s * strainResidual a s)
      ≤ Real.cosh (|strainResidual a s|) := by
  have hη : 0 < strainStepSize a s := strainStepSize_pos a s
  have hηle : strainStepSize a s ≤ 1 := strainStepSize_le_one a s
  have habs : |strainStepSize a s * strainResidual a s|
      ≤ |strainResidual a s| := by
    rw [abs_mul, abs_of_nonneg hη.le]
    calc strainStepSize a s * |strainResidual a s|
        ≤ 1 * |strainResidual a s| :=
          mul_le_mul_of_nonneg_right hηle (abs_nonneg _)
      _ = |strainResidual a s| := one_mul _
  rw [← Real.cosh_abs (strainStepSize a s * strainResidual a s)]
  exact cosh_le_cosh_of_nonneg_of_le (abs_nonneg _) habs

/-- **The correction is at most half the tangent descent.** -/
theorem correction_le_half (a s : ℝ) :
    Real.cosh s * (Real.cosh (strainStepSize a s * strainResidual a s) - 1)
      - Real.sinh s * (Real.sinh (strainStepSize a s * strainResidual a s)
          - strainStepSize a s * strainResidual a s)
    ≤ (strainStepSize a s / 2) * strainResidual a s ^ 2 := by
  set η := strainStepSize a s with hηdef
  set g := strainResidual a s with hgdef
  have hηpos : 0 < η := strainStepSize_pos a s
  have hηle : η ≤ 1 := strainStepSize_le_one a s
  set B := Real.cosh s / 2 + |Real.sinh s| * |g| / 6 with hBdef
  have hBnn : (0:ℝ) ≤ B := by
    rw [hBdef]
    have h1 := Real.one_le_cosh s
    have h2 : (0:ℝ) ≤ |Real.sinh s| * |g| / 6 := by positivity
    linarith
  have hT1 : Real.cosh s * (Real.cosh (η * g) - 1)
      ≤ Real.cosh s * (((η * g) ^ 2 / 2) * Real.cosh (η * g)) :=
    mul_le_mul_of_nonneg_left (cosh_sub_one_le_sq_half_cosh (η * g))
      (zero_le_one.trans (Real.one_le_cosh s))
  have hT2 : -(Real.sinh s * (Real.sinh (η * g) - η * g))
      ≤ |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g)) :=
    calc -(Real.sinh s * (Real.sinh (η * g) - η * g))
        ≤ |Real.sinh s * (Real.sinh (η * g) - η * g)| := neg_le_abs _
      _ = |Real.sinh s| * |Real.sinh (η * g) - η * g| := abs_mul _ _
      _ ≤ |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g)) :=
          mul_le_mul_of_nonneg_left (abs_sinh_sub_self_le_sixth (η * g))
            (abs_nonneg _)
  have hT12 : Real.cosh s * (((η * g) ^ 2 / 2) * Real.cosh (η * g))
      + |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g))
      ≤ Real.cosh (η * g) * (η ^ 2 * g ^ 2) * B := by
    have hη2 : |η| = η := abs_of_nonneg hηpos.le
    have hexp : (η * g) ^ 2 = η ^ 2 * g ^ 2 := by ring
    have habs3 : |η * g| ^ 3 ≤ η ^ 2 * (g ^ 2 * |g|) := by
      have hη3 : η ^ 3 ≤ η ^ 2 := by
        have hη2nn : (0:ℝ) ≤ η ^ 2 := by positivity
        calc η ^ 3 = η ^ 2 * η := by ring
          _ ≤ η ^ 2 * 1 := mul_le_mul_of_nonneg_left hηle hη2nn
          _ = η ^ 2 := mul_one _
      calc |η * g| ^ 3 = (η * |g|) ^ 3 := by rw [abs_mul, hη2]
        _ = η ^ 3 * |g| ^ 3 := by ring
        _ ≤ η ^ 2 * |g| ^ 3 := mul_le_mul_of_nonneg_right hη3 (by positivity)
        _ = η ^ 2 * (g ^ 2 * |g|) := by rw [← sq_abs g]; ring
    have hT1eq : Real.cosh s * (((η * g) ^ 2 / 2) * Real.cosh (η * g))
        = Real.cosh (η * g) * (η ^ 2 * g ^ 2) * (Real.cosh s / 2) := by
      rw [hexp]; ring
    have hT2le : |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g))
        ≤ Real.cosh (η * g) * (η ^ 2 * g ^ 2) * (|g| * |Real.sinh s| / 6) := by
      have hnn : (0:ℝ) ≤ |Real.sinh s| * Real.cosh (η * g) := by positivity
      calc |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g))
          = |Real.sinh s| * Real.cosh (η * g) * (|η * g| ^ 3 / 6) := by ring
        _ ≤ |Real.sinh s| * Real.cosh (η * g) * ((η ^ 2 * (g ^ 2 * |g|)) / 6) :=
            mul_le_mul_of_nonneg_left (by linarith [habs3] :
              |η * g| ^ 3 / 6 ≤ (η ^ 2 * (g ^ 2 * |g|)) / 6) hnn
        _ = Real.cosh (η * g) * (η ^ 2 * g ^ 2) * (|g| * |Real.sinh s| / 6) := by ring
    calc Real.cosh s * (((η * g) ^ 2 / 2) * Real.cosh (η * g))
        + |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g))
        = Real.cosh (η * g) * (η ^ 2 * g ^ 2) * (Real.cosh s / 2)
          + |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g)) := by
          rw [hT1eq]
      _ ≤ Real.cosh (η * g) * (η ^ 2 * g ^ 2) * (Real.cosh s / 2)
          + Real.cosh (η * g) * (η ^ 2 * g ^ 2) * (|g| * |Real.sinh s| / 6) :=
          add_le_add le_rfl hT2le
      _ = Real.cosh (η * g) * (η ^ 2 * g ^ 2) * B := by rw [hBdef]; ring
  have henvm : Real.cosh (η * g) ≤ Real.cosh |g| :=
    cosh_step_le_cosh_abs_residual a s
  have hkey : Real.cosh |g| * (η ^ 2 * g ^ 2) * B ≤ (η / 2) * g ^ 2 := by
    have hE : 2 * B * Real.cosh |g| ≤ strainEnvelope a s := le_max_left _ _
    have hηE : η * (2 * B * Real.cosh |g|) ≤ 1 := by
      rw [hηdef, strainStepSize]
      rw [inv_mul_le_iff₀ (strainEnvelope_pos a s)]
      calc 2 * B * Real.cosh |g| ≤ strainEnvelope a s := hE
        _ = strainEnvelope a s * 1 := (mul_one _).symm
    have hhalf : η * B * Real.cosh |g| ≤ 1 / 2 := by
      have h2 : η * (2 * B * Real.cosh |g|) = 2 * (η * B * Real.cosh |g|) := by ring
      rw [h2] at hηE
      linarith
    by_cases hg0 : g = 0
    · rw [hg0]
      simp
    · have hg2 : (0:ℝ) < g ^ 2 := sq_pos_of_ne_zero hg0
      have hdiv : Real.cosh |g| * (η ^ 2 * g ^ 2) * B
          = (η * g ^ 2) * (η * B * Real.cosh |g|) := by ring
      rw [hdiv]
      calc (η * g ^ 2) * (η * B * Real.cosh |g|)
          ≤ (η * g ^ 2) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hhalf (by positivity)
        _ = (η / 2) * g ^ 2 := by ring
  calc Real.cosh s * (Real.cosh (η * g) - 1)
      - Real.sinh s * (Real.sinh (η * g) - η * g)
      ≤ Real.cosh s * (((η * g) ^ 2 / 2) * Real.cosh (η * g))
        + |Real.sinh s| * ((|η * g| ^ 3 / 6) * Real.cosh (η * g)) :=
        add_le_add hT1 hT2
    _ ≤ Real.cosh (η * g) * (η ^ 2 * g ^ 2) * B := hT12
    _ ≤ Real.cosh |g| * (η ^ 2 * g ^ 2) * B :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right henvm (by positivity)) hBnn
    _ ≤ (η / 2) * g ^ 2 := hkey

/-- **THEOREM (the Lyapunov decrease).** -/
theorem descent_one_dim (a s : ℝ) :
    sourceCost1 a (strainStep1 a s) - sourceCost1 a s
      ≤ -(strainStepSize a s / 2) * strainResidual a s ^ 2 := by
  rw [step_one_dim_sub]
  have h := correction_le_half a s
  linarith [h]

/-- **THEOREM (strict decrease off the stationary point).** -/
theorem descent_one_dim_lt (a s : ℝ) (hs : strainResidual a s ≠ 0) :
    sourceCost1 a (strainStep1 a s) < sourceCost1 a s := by
  have h := descent_one_dim a s
  have hg2 : (0:ℝ) < strainResidual a s ^ 2 := sq_pos_of_ne_zero hs
  have hη : (0:ℝ) < strainStepSize a s / 2 := by
    have := strainStepSize_pos a s
    positivity
  have hneg : -(strainStepSize a s / 2) * strainResidual a s ^ 2 < 0 := by
    have hpos : (0:ℝ) < (strainStepSize a s / 2) * strainResidual a s ^ 2 := by
      positivity
    linarith
  linarith

/-- **THEOREM (fixed points).** The step's fixed points are exactly the
sourced stationary point. -/
theorem step_fixed_iff_arsinh (a s : ℝ) :
    strainStep1 a s = s ↔ s = Real.arsinh a := by
  constructor
  · intro h
    unfold strainStep1 at h
    have hg : strainStepSize a s * strainResidual a s = 0 := by linarith
    have hg2 : strainResidual a s = 0 :=
      (mul_eq_zero.mp hg).resolve_left (strainStepSize_pos a s).ne'
    have hsinh : Real.sinh s = a := by
      unfold strainResidual at hg2
      linarith
    rw [← Real.sinh_arsinh a] at hsinh
    exact Real.sinh_injective hsinh
  · intro h
    rw [h]
    unfold strainStep1 strainResidual
    rw [Real.sinh_arsinh]
    simp

/-! ## §3. The contraction -/

/-- |sinh x| = sinh |x|. -/
theorem abs_sinh_eq_sinh_abs (x : ℝ) : |Real.sinh x| = Real.sinh |x| := by
  rcases le_or_gt 0 x with h | h
  · have h2 : 0 ≤ Real.sinh x := by
      have := Real.sinh_strictMono.monotone (show (0:ℝ) ≤ x from h)
      simpa using this
    rw [abs_of_nonneg h, abs_of_nonneg h2]
  · have h2 : Real.sinh x < 0 := by
      have := Real.sinh_strictMono (show x < 0 from h)
      simpa using this
    rw [abs_of_neg h, abs_of_neg h2, Real.sinh_neg]

/-- **THEOREM (the contraction).** One step contracts the distance to the
sourced stationary point by `1 - η`. -/
theorem contraction_one_dim (a s : ℝ) :
    |strainStep1 a s - Real.arsinh a|
      ≤ (1 - strainStepSize a s) * |s - Real.arsinh a| := by
  set sstar := Real.arsinh a with hsstar
  set η := strainStepSize a s with hηdef
  set g := strainResidual a s with hgdef
  have ha : a = Real.sinh sstar := by rw [hsstar, Real.sinh_arsinh]
  have hηpos : 0 < η := strainStepSize_pos a s
  by_cases hs : s = sstar
  · rw [hs]
    have hg0 : strainResidual a sstar = 0 := by
      unfold strainResidual
      rw [Real.sinh_arsinh]
      simp
    have hstep0 : strainStep1 a sstar = sstar := by
      unfold strainStep1
      rw [hg0]
      simp
    rw [hstep0]
    simp
  · -- MVT for sinh between s and s*.
    have hsub : Real.sinh s - Real.sinh sstar = g := by
      rw [hgdef]
      unfold strainResidual
      rw [ha]
    have hmvt : ∃ ξ : ℝ, ξ ∈ Set.Ioo (min s sstar) (max s sstar) ∧
        Real.cosh ξ = (Real.sinh s - Real.sinh sstar) / (s - sstar) := by
      rcases lt_or_gt_of_ne hs with hlt | hgt
      · have h := exists_deriv_eq_slope Real.sinh (show s < sstar from hlt)
          Real.continuous_sinh.continuousOn
          (Real.differentiable_sinh.differentiableOn)
        obtain ⟨ξ, hξ, hξeq⟩ := h
        refine ⟨ξ, ?_, ?_⟩
        · rw [min_eq_left hlt.le, max_eq_right hlt.le]
          exact hξ
        · rw [Real.deriv_sinh] at hξeq
          rw [hξeq, div_eq_div_iff (sub_ne_zero.mpr hlt.ne') (sub_ne_zero.mpr hlt.ne)]
          ring
      · have h := exists_deriv_eq_slope Real.sinh (show sstar < s from hgt)
          Real.continuous_sinh.continuousOn
          (Real.differentiable_sinh.differentiableOn)
        obtain ⟨ξ, hξ, hξeq⟩ := h
        refine ⟨ξ, ?_, ?_⟩
        · rw [min_eq_right hgt.le, max_eq_left hgt.le]
          exact hξ
        · rw [Real.deriv_sinh] at hξeq
          exact hξeq
    obtain ⟨ξ, hξmem, hξeq⟩ := hmvt
    have hgc : g = Real.cosh ξ * (s - sstar) := by
      rw [← hsub, hξeq]
      field_simp [sub_ne_zero.mpr hs]
    have hg_abs : |g| = Real.cosh ξ * |s - sstar| := by
      rw [hgc, abs_mul, abs_of_pos
        (lt_of_lt_of_le one_pos (Real.one_le_cosh ξ))]
    have hsg : |s - sstar| ≤ |g| := by
      rw [hg_abs]
      calc |s - sstar| = 1 * |s - sstar| := (one_mul _).symm
        _ ≤ Real.cosh ξ * |s - sstar| :=
          mul_le_mul_of_nonneg_right (Real.one_le_cosh ξ) (abs_nonneg _)
    have hξle : |ξ| ≤ |s| + |g| := by
      have hM : |ξ| ≤ max |s| |sstar| := by
        rw [abs_le]
        constructor
        · have hneg : -(max |s| |sstar|) = min (-|s|) (-|sstar|) := by
            rcases le_total |s| |sstar| with h | h
            · rw [max_eq_right h, min_eq_right (neg_le_neg h)]
            · rw [max_eq_left h, min_eq_left (neg_le_neg h)]
          calc -(max |s| |sstar|) = min (-|s|) (-|sstar|) := hneg
            _ ≤ min s sstar := min_le_min (neg_abs_le s) (neg_abs_le sstar)
            _ ≤ ξ := hξmem.1.le
        · calc ξ ≤ max s sstar := hξmem.2.le
            _ ≤ max |s| |sstar| := max_le_max (le_abs_self s) (le_abs_self sstar)
      have hS : |sstar| ≤ |s| + |g| := by
        calc |sstar| = |sstar - s + s| := by ring_nf
          _ ≤ |sstar - s| + |s| := abs_add_le _ _
          _ = |s - sstar| + |s| := by rw [abs_sub_comm]
          _ ≤ |g| + |s| := add_le_add_left hsg |s|
          _ = |s| + |g| := add_comm _ _
      calc |ξ| ≤ max |s| |sstar| := hM
        _ ≤ |s| + |g| := max_le (le_add_of_nonneg_right (abs_nonneg _)) hS
    have hstep : strainStep1 a s - sstar = (s - sstar) * (1 - η * Real.cosh ξ) := by
      unfold strainStep1
      rw [← hηdef, ← hgdef, hgc]
      ring
    rw [hstep]
    have hηc : η * Real.cosh (|s| + |g|) ≤ 1 := by
      rw [hηdef, strainStepSize]
      rw [inv_mul_le_iff₀ (strainEnvelope_pos a s)]
      calc Real.cosh (|s| + |g|) ≤ strainEnvelope a s := le_max_right _ _
        _ = strainEnvelope a s * 1 := (mul_one _).symm
    have hcξ : Real.cosh ξ ≤ Real.cosh (|s| + |g|) := by
      rw [← Real.cosh_abs ξ]
      exact cosh_le_cosh_of_nonneg_of_le (abs_nonneg _) hξle
    have hfactor : |1 - η * Real.cosh ξ| ≤ 1 - η := by
      have h1 : (1:ℝ) ≤ Real.cosh ξ := Real.one_le_cosh ξ
      have hlo : η ≤ η * Real.cosh ξ := by
        calc η = η * 1 := (mul_one _).symm
          _ ≤ η * Real.cosh ξ := mul_le_mul_of_nonneg_left h1 hηpos.le
      have hhi : η * Real.cosh ξ ≤ 1 := le_trans
        (mul_le_mul_of_nonneg_left hcξ hηpos.le) hηc
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - η * Real.cosh ξ)]
      linarith
    calc |(s - sstar) * (1 - η * Real.cosh ξ)|
        = |s - sstar| * |1 - η * Real.cosh ξ| := abs_mul _ _
      _ ≤ |s - sstar| * (1 - η) :=
          mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
      _ = (1 - η) * |s - sstar| := mul_comm _ _

/-! ## §4. The orbit and convergence -/

/-- The strain orbit: iterate the step. -/
noncomputable def strainOrbit (a : ℝ) (s₀ : ℝ) : ℕ → ℝ
  | 0 => s₀
  | k + 1 => strainStep1 a (strainOrbit a s₀ k)

/-- **THEOREM (geometric convergence).** -/
theorem strainOrbit_abs_le (a : ℝ) (s₀ : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ k : ℕ,
      |strainOrbit a s₀ k - Real.arsinh a| ≤ q ^ k * |s₀ - Real.arsinh a| := by
  set sstar := Real.arsinh a with hsstar
  set M := |sstar| + |s₀ - sstar| with hMdef
  set G := Real.sinh M + |a| with hGdef
  set E2 := 2 * (Real.cosh M + Real.sinh M * G / 6) * Real.cosh G
    + Real.cosh (M + G) with hE2def
  set q := 1 - E2⁻¹ with hqdef
  have hMnn : 0 ≤ M := by rw [hMdef]; positivity
  have hsinhM : 0 ≤ Real.sinh M := by
    simpa using Real.sinh_strictMono.monotone hMnn
  have hGnn : 0 ≤ G := by rw [hGdef]; linarith [hsinhM, abs_nonneg a]
  have hprod_nn : (0:ℝ) ≤ 2 * (Real.cosh M + Real.sinh M * G / 6) * Real.cosh G := by
    have h1 : (0:ℝ) ≤ Real.sinh M * G := mul_nonneg hsinhM hGnn
    have h2 : (0:ℝ) ≤ Real.cosh M + Real.sinh M * G / 6 := by
      linarith [Real.one_le_cosh M, h1]
    have h3 : (0:ℝ) ≤ Real.cosh G := le_trans zero_le_one (Real.one_le_cosh G)
    exact mul_nonneg (mul_nonneg (by norm_num) h2) h3
  have hE2pos : 0 < E2 := by
    rw [hE2def]
    linarith [hprod_nn, Real.one_le_cosh (M + G)]
  have hq0 : 0 ≤ q := by
    have h1 : E2⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      rw [hE2def]
      linarith [hprod_nn, Real.one_le_cosh (M + G)]
    linarith
  have hq1 : q < 1 := by
    have h1 : (0:ℝ) < E2⁻¹ := by positivity
    linarith
  refine ⟨q, hq0, hq1, ?_⟩
  intro k
  induction k with
  | zero => simp [strainOrbit]
  | succ k ih =>
      have hbound : |strainOrbit a s₀ k| ≤ M := by
        have hd : |strainOrbit a s₀ k - sstar| ≤ |s₀ - sstar| := by
          exact le_trans ih (by
            have hq1' : q ^ k ≤ 1 := pow_le_one₀ hq0 (le_of_lt hq1)
            calc q ^ k * |s₀ - sstar| ≤ 1 * |s₀ - sstar| :=
                mul_le_mul_of_nonneg_right hq1' (abs_nonneg _)
              _ = |s₀ - sstar| := one_mul _)
        calc |strainOrbit a s₀ k|
            = |sstar + (strainOrbit a s₀ k - sstar)| := by ring_nf
          _ ≤ |sstar| + |strainOrbit a s₀ k - sstar| := abs_add_le _ _
          _ ≤ |sstar| + |s₀ - sstar| := add_le_add_right hd |sstar|
          _ = M := rfl
      have hηk : E2⁻¹ ≤ strainStepSize a (strainOrbit a s₀ k) := by
        have hE : strainEnvelope a (strainOrbit a s₀ k) ≤ E2 := by
          apply max_le
          · have hcosh : Real.cosh (strainOrbit a s₀ k) ≤ Real.cosh M := by
              rw [← Real.cosh_abs (strainOrbit a s₀ k)]
              exact cosh_le_cosh_of_nonneg_of_le (abs_nonneg _) hbound
            have hsinh : |Real.sinh (strainOrbit a s₀ k)| ≤ Real.sinh M := by
              rw [abs_sinh_eq_sinh_abs]
              exact Real.sinh_strictMono.monotone hbound
            have hg : |strainResidual a (strainOrbit a s₀ k)| ≤ G := by
              unfold strainResidual
              calc |Real.sinh (strainOrbit a s₀ k) - a|
                  ≤ |Real.sinh (strainOrbit a s₀ k)| + |a| := abs_sub _ _
                _ ≤ Real.sinh M + |a| := add_le_add hsinh le_rfl
                _ = G := rfl
            have hprod : |Real.sinh (strainOrbit a s₀ k)|
                * |strainResidual a (strainOrbit a s₀ k)| ≤ Real.sinh M * G :=
              mul_le_mul hsinh hg (abs_nonneg _)
                (by simpa using Real.sinh_strictMono.monotone hMnn)
            calc 2 * (Real.cosh (strainOrbit a s₀ k) / 2
                + |Real.sinh (strainOrbit a s₀ k)|
                  * |strainResidual a (strainOrbit a s₀ k)| / 6)
                * Real.cosh (|strainResidual a (strainOrbit a s₀ k)|)
                ≤ 2 * (Real.cosh M + Real.sinh M * G / 6) * Real.cosh G := by
                  apply mul_le_mul
                  · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
                    linarith [hcosh, hprod, Real.one_le_cosh M]
                  · exact cosh_le_cosh_of_nonneg_of_le (abs_nonneg _) hg
                  · positivity
                  · positivity
              _ ≤ 2 * (Real.cosh M + Real.sinh M * G / 6) * Real.cosh G
                  + Real.cosh (M + G) :=
                  le_add_of_nonneg_right (by positivity :
                    (0:ℝ) ≤ Real.cosh (M + G))
              _ = E2 := rfl
          · have hsinh : |Real.sinh (strainOrbit a s₀ k)| ≤ Real.sinh M := by
              rw [abs_sinh_eq_sinh_abs]
              exact Real.sinh_strictMono.monotone hbound
            have hg : |strainResidual a (strainOrbit a s₀ k)| ≤ G := by
              unfold strainResidual
              calc |Real.sinh (strainOrbit a s₀ k) - a|
                  ≤ |Real.sinh (strainOrbit a s₀ k)| + |a| := abs_sub _ _
                _ ≤ Real.sinh M + |a| := add_le_add hsinh le_rfl
                _ = G := rfl
            calc Real.cosh (|strainOrbit a s₀ k|
                + |strainResidual a (strainOrbit a s₀ k)|)
                ≤ Real.cosh (M + G) :=
                  cosh_le_cosh_of_nonneg_of_le (by positivity)
                    (add_le_add hbound hg)
              _ ≤ 2 * (Real.cosh M + Real.sinh M * G / 6) * Real.cosh G
                  + Real.cosh (M + G) :=
                  le_add_of_nonneg_left (by positivity :
                    (0:ℝ) ≤ 2 * (Real.cosh M + Real.sinh M * G / 6) * Real.cosh G)
              _ = E2 := rfl
        rw [strainStepSize]
        exact (inv_le_inv₀ hE2pos (strainEnvelope_pos _ _)).mpr hE
      have hstep := contraction_one_dim a (strainOrbit a s₀ k)
      calc |strainStep1 a (strainOrbit a s₀ k) - sstar|
          ≤ (1 - strainStepSize a (strainOrbit a s₀ k))
            * |strainOrbit a s₀ k - sstar| := hstep
        _ ≤ (1 - E2⁻¹) * |strainOrbit a s₀ k - sstar| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            linarith [hηk]
        _ ≤ (1 - E2⁻¹) * (q ^ k * |s₀ - sstar|) :=
            mul_le_mul_of_nonneg_left ih (by linarith [hq0, hq1])
        _ = q ^ (k + 1) * |s₀ - sstar| := by rw [hqdef, pow_succ]; ring

/-- **THEOREM (convergence to the sourced stationary point).** -/
theorem strainOrbit_tendsto (a : ℝ) (s₀ : ℝ) :
    Tendsto (strainOrbit a s₀) atTop (𝓝 (Real.arsinh a)) := by
  obtain ⟨q, hq0, hq1, hbound⟩ := strainOrbit_abs_le a s₀
  rw [tendsto_iff_dist_tendsto_zero]
  have hgeom : Tendsto (fun k => q ^ k * |s₀ - Real.arsinh a|) atTop (𝓝 0) := by
    have hpow : Tendsto (fun k => q ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have := hpow.mul_const |s₀ - Real.arsinh a|
    simpa [zero_mul] using this
  have habs := (squeeze_zero (fun k => abs_nonneg _) hbound hgeom).abs
  simpa [Real.dist_eq, abs_zero] using habs

/-! ## §5. The vector form on the link -/

/-- The componentwise step on the link. -/
noncomputable def strainStepVec (n : ℕ) (c : ℝ) (t : Fin n → ℝ) : Fin n → ℝ :=
  fun i => strainStep1 (c / n) (t i)

/-- The sourced action is the sum of the per-channel costs. -/
theorem sourcedAction_eq_sum_sourceCost1 (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    sourcedAction n c t = ∑ i, sourceCost1 (c / n) (t i) := by
  unfold sourceCost1
  exact sourcedAction_eq_sum n c t

/-- **THEOREM (the sourced action decreases).** -/
theorem sourcedAction_step_le (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    sourcedAction n c (strainStepVec n c t)
      ≤ sourcedAction n c t
        - (1/2) * ∑ i, strainStepSize (c / n) (t i)
          * strainResidual (c / n) (t i) ^ 2 := by
  rw [sourcedAction_eq_sum_sourceCost1, sourcedAction_eq_sum_sourceCost1]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := descent_one_dim (c / n) (t i)
  show sourceCost1 (c / n) (strainStep1 (c / n) (t i))
      ≤ sourceCost1 (c / n) (t i)
        - 1 / 2 * (strainStepSize (c / n) (t i) * strainResidual (c / n) (t i) ^ 2)
  linarith

/-- **THEOREM (strict decrease of the sourced action off the minimizer).** -/
theorem sourcedAction_step_lt (n : ℕ) (c : ℝ) (t : Fin n → ℝ)
    (h : ∃ i, strainResidual (c / n) (t i) ≠ 0) :
    sourcedAction n c (strainStepVec n c t) < sourcedAction n c t := by
  rw [sourcedAction_eq_sum_sourceCost1, sourcedAction_eq_sum_sourceCost1,
    ← sub_neg, ← Finset.sum_sub_distrib,
    show (0 : ℝ) = ∑ i : Fin n, (0 : ℝ) from (Finset.sum_const_zero).symm]
  obtain ⟨i, hi⟩ := h
  apply Finset.sum_lt_sum
  · intro j _
    calc sourceCost1 (c / n) (strainStep1 (c / n) (t j))
        - sourceCost1 (c / n) (t j)
        ≤ -(strainStepSize (c / n) (t j) / 2)
          * strainResidual (c / n) (t j) ^ 2 :=
          descent_one_dim (c / n) (t j)
      _ ≤ 0 := by
          have hη : 0 < strainStepSize (c / n) (t j) := strainStepSize_pos _ _
          have hg : (0:ℝ) ≤ strainResidual (c / n) (t j) ^ 2 := by positivity
          nlinarith [hη, hg]
  · exact ⟨i, Finset.mem_univ i, sub_neg.mpr (descent_one_dim_lt (c / n) (t i) hi)⟩

/-- **THEOREM (fixed points of the vector step).** -/
theorem stepVec_fixed_iff_minimizer (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    strainStepVec n c t = t ↔ t = sourcedMinimizer n c := by
  constructor
  · intro h
    funext i
    have hi : strainStep1 (c / n) (t i) = t i := congrFun h i
    exact (step_fixed_iff_arsinh (c / n) (t i)).mp hi
  · intro h
    rw [h]
    funext i
    exact (step_fixed_iff_arsinh (c / n) _).mpr rfl

/-- The componentwise orbit on the link. -/
noncomputable def strainStepVecOrbit (n : ℕ) (c : ℝ) (t : Fin n → ℝ) :
    ℕ → (Fin n → ℝ)
  | 0 => t
  | k + 1 => strainStepVec n c (strainStepVecOrbit n c t k)

/-- The componentwise orbit is the per-channel orbit. -/
theorem strainStepVecOrbit_apply (n : ℕ) (c : ℝ) (t : Fin n → ℝ) (k : ℕ)
    (i : Fin n) :
    strainStepVecOrbit n c t k i = strainOrbit (c / n) (t i) k := by
  induction k with
  | zero => rfl
  | succ j ih =>
      show strainStep1 (c / n) (strainStepVecOrbit n c t j i)
          = strainStep1 (c / n) (strainOrbit (c / n) (t i) j)
      rw [ih]

/-- **THEOREM (each channel converges to the minimizer).** -/
theorem strainStepVec_tendsto_minimizer (n : ℕ) (c : ℝ) (t : Fin n → ℝ)
    (i : Fin n) :
    Tendsto (fun k => strainStepVecOrbit n c t k i) atTop
      (𝓝 (Real.arsinh (c / n))) := by
  rw [show (fun k => strainStepVecOrbit n c t k i)
      = (fun k => strainOrbit (c / n) (t i) k) from
    funext (strainStepVecOrbit_apply n c t · i)]
  exact strainOrbit_tendsto _ _

end

end StrainDescent
end SevenGaps
end Gravity
end IndisputableMonolith

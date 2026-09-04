import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Recognition Kernel: continuity shrink attempt

Does calibration plus the composition law force continuity of `F` on `(0, ∞)`?

**Yes** (`composition_calibration_forces_continuity`, 2026-07-25). So continuity is
redundant and was deleted from `RecognitionKernel`, taking it from seven members to
six.

## Why it works, and why the classical intuition says otherwise

A d'Alembert equation without a regularity assumption has wild solutions built from
a Hamel basis, which is why the paper statement of the cost theorem assumes
continuity. Those solutions are nowhere differentiable, and in Lean `deriv` returns
the junk value `0` off the differentiability set, so `IsCalibrated F`, which asserts
`deriv (deriv (G F)) 0 = 1`, cannot hold for any of them. Lean's calibration is
therefore strictly stronger than "the log-curvature is 1" reads on paper: it silently
carries local regularity, and that is enough to run the argument.

## The chain

1. `calibrated_differentiable_punctured`: calibration forces `G F` differentiable on
   a punctured window, because `deriv (G F) t / t → 1` keeps the derivative nonzero
   off the origin, and a nonzero `deriv` cannot be a junk value.
2. `calibrated_deriv_pos_right`: the same quotient is positive on a right window, so
   `calibrated_strictMonoOn_right` gives strict monotonicity there.
3. `dAlembert_ge_neg_one`: every d'Alembert solution satisfies `H ≥ -1`, from
   `H (2t) + 1 = 2 (H t)²` at `t = s/2`. The bound is free, needs no regularity, and
   is exactly the boundedness a monotone-limit argument wants.
4. Monotone plus bounded gives a one-sided limit (`calibrated_tendsto_G_right`).
5. `calibrated_tendsto_H_one_right`: two instances of the functional equation pin the
   limit's value. At `(t, t)` it gives `M + 1 = 2M²` and at `(2t, t)` it gives
   `2M = 2M²`, so `M = 1` with no case split. One instance alone would leave the
   second root `M = -1/2` alive, which is the trap in this step.
6. Evenness transports the limit to the left, and `H F 0 = 1` closes it up to a
   genuine `ContinuousAt`, feeding the ladder that was already in place.

Normalization is restated locally (same proof as
`KernelIndependence.composition_calibration_forces_normalized`) so this module
stays slim and does not pull `MeasureForcing`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace KernelContinuity

open Cost.FunctionalEquation
open Filter Topology Set

noncomputable section

/-! ## Step 1: calibration forces punctured differentiability of `G F` -/

/-- Calibration forces genuine differentiability of `deriv (G F)` at `0`:
the junk value of `deriv` is `0`, so it cannot equal `1`. -/
theorem calibrated_differentiableAt_deriv
    (F : ℝ → ℝ) (hCalib : IsCalibrated F) :
    DifferentiableAt ℝ (deriv (G F)) 0 := by
  by_contra h
  have hzero : deriv (deriv (G F)) 0 = 0 := deriv_zero_of_not_differentiableAt h
  have hcal : deriv (deriv (G F)) 0 = 1 := hCalib
  rw [hzero] at hcal
  exact absurd hcal (by norm_num)

/-- Calibration is a genuine `HasDerivAt` statement for the first log-derivative. -/
theorem calibrated_hasDerivAt_deriv
    (F : ℝ → ℝ) (hCalib : IsCalibrated F) :
    HasDerivAt (deriv (G F)) 1 0 := by
  have hdiff := calibrated_differentiableAt_deriv F hCalib
  have h := hdiff.hasDerivAt
  rwa [hCalib] at h

/-- Near `0`, the first log-derivative cannot vanish off `0`.
If `deriv (G F) t = 0` for arbitrarily small `t ≠ 0`, the difference quotient
would be `-deriv (G F) 0 / t`, which cannot tend to `1`. -/
theorem calibrated_deriv_ne_zero_nearby
    (F : ℝ → ℝ) (hCalib : IsCalibrated F) :
    ∃ ε > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε → deriv (G F) t ≠ 0 := by
  have hder := calibrated_hasDerivAt_deriv F hCalib
  have hslope := (hasDerivAt_iff_tendsto_slope).1 hder
  -- Choose ε so that the slope is within 1/2 of 1, and also |t| < |f₀|/3 when f₀ ≠ 0.
  let δ₀ : ℝ := |deriv (G F) 0| / 3
  have hnhds :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), |slope (deriv (G F)) 0 t - 1| < (1 / 2 : ℝ) := by
    have := Metric.tendsto_nhds.1 hslope (1 / 2 : ℝ) (by norm_num)
    simpa [Real.dist_eq] using this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnhds
  obtain ⟨ε₀, hε₀, hball⟩ := hnhds
  by_cases h0 : deriv (G F) 0 = 0
  · -- f₀ = 0: slope = (f t)/t; if f t = 0 then slope = 0, distance to 1 is 1.
    refine ⟨ε₀, hε₀, fun t ht hlt => ?_⟩
    intro hzero
    have hslt : |slope (deriv (G F)) 0 t - 1| < (1 / 2 : ℝ) := by
      have : dist t (0 : ℝ) < ε₀ := by simpa [Real.dist_eq] using hlt
      exact hball this ht
    have : |((deriv (G F) t - deriv (G F) 0) / t) - 1| < (1 / 2 : ℝ) := by
      simpa [slope_def_field] using hslt
    simp [hzero, h0] at this
    linarith
  · -- f₀ ≠ 0: take ε = min(ε₀, |f₀|/3).
    have hδ₀ : 0 < δ₀ := by
      dsimp [δ₀]
      positivity
    let ε : ℝ := min ε₀ δ₀
    have hε : 0 < ε := lt_min hε₀ hδ₀
    refine ⟨ε, hε, fun t ht hlt => ?_⟩
    intro hzero
    have hlt₀ : |t| < ε₀ := hlt.trans_le (min_le_left _ _)
    have hltδ : |t| < δ₀ := hlt.trans_le (min_le_right _ _)
    have hslt : |slope (deriv (G F)) 0 t - 1| < (1 / 2 : ℝ) := by
      have : dist t (0 : ℝ) < ε₀ := by simpa [Real.dist_eq] using hlt₀
      exact hball this ht
    have hquot : |(0 - deriv (G F) 0) / t - 1| < (1 / 2 : ℝ) := by
      have : |(deriv (G F) t - deriv (G F) 0) / t - 1| < (1 / 2 : ℝ) := by
        simpa [slope_def_field] using hslt
      simpa [hzero] using this
    -- From |a - 1| < 1/2 with a = (0 - f₀)/t = -f₀/t, get |f₀/t| < 3/2.
    have habs_lt : |deriv (G F) 0 / t| < (3 / 2 : ℝ) := by
      have ha : |(-deriv (G F) 0) / t - 1| < (1 / 2 : ℝ) := by
        simpa [zero_sub, neg_div] using hquot
      have hle : |deriv (G F) 0 / t| ≤ |(-deriv (G F) 0) / t - 1| + 1 := by
        calc
          |deriv (G F) 0 / t|
              = |(-deriv (G F) 0) / t| := by simp [abs_div, abs_neg]
          _ = |((-deriv (G F) 0) / t - 1) + 1| := by ring_nf
          _ ≤ |(-deriv (G F) 0) / t - 1| + |(1 : ℝ)| := abs_add_le _ _
          _ = |(-deriv (G F) 0) / t - 1| + 1 := by simp
      exact lt_of_le_of_lt hle (by linarith [ha])
    have hpos : 0 < |t| := abs_pos.mpr ht
    have hfo_lt : |deriv (G F) 0| < (3 / 2 : ℝ) * |t| := by
      have : |deriv (G F) 0| / |t| < (3 / 2 : ℝ) := by simpa [abs_div] using habs_lt
      exact (div_lt_iff₀ hpos).1 this
    have hltδ' : |t| < |deriv (G F) 0| / 3 := by simpa [δ₀] using hltδ
    have hpos0 : 0 < |deriv (G F) 0| := abs_pos.mpr h0
    nlinarith [hfo_lt, hltδ', hpos0]

/-- **Step 1 (crux).** Calibration alone forces `G F` to be differentiable on a
punctured neighbourhood of `0`. -/
theorem calibrated_differentiable_punctured
    (F : ℝ → ℝ) (hCalib : IsCalibrated F) :
    ∃ ε > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε → DifferentiableAt ℝ (G F) t := by
  obtain ⟨ε, hε, hne⟩ := calibrated_deriv_ne_zero_nearby F hCalib
  exact ⟨ε, hε, fun t ht hlt => differentiableAt_of_deriv_ne_zero (hne t ht hlt)⟩

/-! ## Algebraic setup from composition + calibration -/

theorem deriv_H_eq_deriv_G (F : ℝ → ℝ) : deriv (H F) = deriv (G F) := by
  funext t
  change deriv (fun y => G F y + 1) t = deriv (G F) t
  simpa using (deriv_add_const (f := G F) (x := t) (c := (1 : ℝ)))

theorem deriv2_H_eq_deriv2_G (F : ℝ → ℝ) :
    deriv (deriv (H F)) = deriv (deriv (G F)) :=
  congrArg deriv (deriv_H_eq_deriv_G F)

/-- Local restatement of the normalization shrink (keeps this module import-slim). -/
theorem composition_calibration_forces_normalized
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    IsNormalized F := by
  by_contra hne
  have hconst : ∀ x : ℝ, 0 < x → F x = -1 := by
    intro x hx
    have h := hComp x 1 hx one_pos
    rw [mul_one, div_one] at h
    have hquad : F 1 * (F x + 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp hquad with h1 | h2
    · exact absurd h1 hne
    · linarith
  have hG : G F = fun _ : ℝ => (-1 : ℝ) := by
    funext t
    simpa [G] using hconst (Real.exp t) (Real.exp_pos t)
  have hzero : deriv (deriv (G F)) 0 = 0 := by
    rw [hG]
    simp
  have hcal : deriv (deriv (G F)) 0 = 1 := hCalib
  rw [hzero] at hcal
  exact absurd hcal (by norm_num)

/-- Composition plus calibration give the standard d'Alembert equation for `H F`. -/
theorem composition_calibration_dAlembert
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    (H F) 0 = 1 ∧
      (∀ t u : ℝ, H F (t + u) + H F (t - u) = 2 * H F t * H F u) := by
  have hNorm : IsNormalized F :=
    composition_calibration_forces_normalized F hComp hCalib
  have h_H0 : H F 0 = 1 := by
    simp [H, G, IsNormalized] at hNorm ⊢
    linarith [hNorm]
  have hCosh : CoshAddIdentity F := (composition_law_equiv_coshAdd F).mp hComp
  have h_dAlembert : ∀ t u, H F (t + u) + H F (t - u) = 2 * H F t * H F u := by
    intro t u
    have hG := hCosh t u
    have h_goal :
        (G F (t + u) + 1) + (G F (t - u) + 1) = 2 * (G F t + 1) * (G F u + 1) := by
      calc
        (G F (t + u) + 1) + (G F (t - u) + 1)
            = (G F (t + u) + G F (t - u)) + 2 := by ring
        _ = (2 * (G F t * G F u) + 2 * (G F t + G F u)) + 2 := by simpa [hG]
        _ = 2 * (G F t + 1) * (G F u + 1) := by ring
    simpa [H] using h_goal
  exact ⟨h_H0, h_dAlembert⟩

theorem calibrated_H_differentiable_punctured
    (F : ℝ → ℝ) (hCalib : IsCalibrated F) :
    ∃ ε > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε → DifferentiableAt ℝ (H F) t := by
  obtain ⟨ε, hε, hG⟩ := calibrated_differentiable_punctured F hCalib
  refine ⟨ε, hε, fun t ht hlt => ?_⟩
  change DifferentiableAt ℝ (fun s => G F s + 1) t
  exact (hG t ht hlt).add (differentiableAt_const 1)

/-- On the punctured calibration window, `deriv (H F)` is odd. -/
theorem calibrated_deriv_H_odd_nearby
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    ∃ ε > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε → deriv (H F) (-t) = -deriv (H F) t := by
  have ⟨h_H0, h_dAlembert⟩ := composition_calibration_dAlembert F hComp hCalib
  have h_even : Function.Even (H F) := dAlembert_even (H F) h_H0 h_dAlembert
  obtain ⟨ε, hε, hHdiff⟩ := calibrated_H_differentiable_punctured F hCalib
  refine ⟨ε, hε, fun t ht hlt => ?_⟩
  have hneg : DifferentiableAt ℝ (H F) (-t) :=
    hHdiff (-t) (neg_ne_zero.mpr ht) (by simpa [abs_neg] using hlt)
  have hneg_id : DifferentiableAt ℝ (fun x : ℝ => -x) t :=
    differentiable_neg.differentiableAt
  have hchain :
      deriv (H F ∘ fun x : ℝ => -x) t =
        deriv (H F) (-t) * deriv (fun x : ℝ => -x) t :=
    deriv_comp t hneg hneg_id
  have heq : (H F ∘ fun x : ℝ => -x) = H F := by
    funext x
    -- Even: H (-x) = H x
    simpa [Function.comp_apply] using h_even x
  have hrhs : deriv (H F ∘ fun x : ℝ => -x) t = deriv (H F) t := by
    simp [heq]
  have hneg' : deriv (fun x : ℝ => -x) t = -1 := by
    simp
  rw [hchain, hneg'] at hrhs
  linarith

/-- The first derivative of `H F` tends to `0` at `0`. -/
theorem calibrated_tendsto_deriv_H_zero
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    Tendsto (deriv (H F)) (𝓝 0) (𝓝 0) := by
  have hderG := calibrated_hasDerivAt_deriv F hCalib
  have hderiv_eq := deriv_H_eq_deriv_G F
  have hcont : Tendsto (deriv (G F)) (𝓝 0) (𝓝 (deriv (G F) 0)) :=
    hderG.continuousAt.tendsto
  obtain ⟨ε, hε, hodd⟩ := calibrated_deriv_H_odd_nearby F hComp hCalib
  have hG0 : deriv (G F) 0 = 0 := by
    have hlim : Tendsto (deriv (H F)) (𝓝 0) (𝓝 (deriv (G F) 0)) := by
      simpa [hderiv_eq] using hcont
    have hlim_neg :
        Tendsto (fun t : ℝ => deriv (H F) (-t)) (𝓝 0) (𝓝 (deriv (G F) 0)) := by
      have hmap : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg : Continuous fun t : ℝ => -t).tendsto 0
      exact hlim.comp hmap
    have hlim_neg' :
        Tendsto (fun t : ℝ => -deriv (H F) t) (𝓝 0) (𝓝 (-deriv (G F) 0)) :=
      hlim.neg
    have heq_ev :
        ∀ᶠ t in 𝓝[≠] (0 : ℝ), deriv (H F) (-t) = -deriv (H F) t := by
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨ε, hε, fun t ht ht0 => ?_⟩
      exact hodd t ht0 (by simpa [Real.dist_eq] using ht)
    have hlim_neg_within :
        Tendsto (fun t : ℝ => deriv (H F) (-t)) (𝓝[≠] (0 : ℝ))
          (𝓝 (deriv (G F) 0)) :=
      hlim_neg.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    have hlim_neg'_within :
        Tendsto (fun t : ℝ => -deriv (H F) t) (𝓝[≠] (0 : ℝ))
          (𝓝 (-deriv (G F) 0)) :=
      hlim_neg'.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℝ)ᶜ))
    have heq_tendsto :
        Tendsto (fun t : ℝ => deriv (H F) (-t)) (𝓝[≠] (0 : ℝ))
          (𝓝 (-deriv (G F) 0)) :=
      Tendsto.congr' (heq_ev.mono fun _ ht => ht.symm) hlim_neg'_within
    have huniq := tendsto_nhds_unique hlim_neg_within heq_tendsto
    linarith [huniq]
  simpa [hderiv_eq, hG0] using hcont

/-- Continuity of a d'Alembert solution from `Tendsto H (nhds 0) (nhds 1)`.
Extracted from `dAlembert_continuous_of_log_curvature`, which only used log-curvature
to obtain this tendsto. -/
theorem dAlembert_continuous_of_tendsto_at_zero
    (Hf : ℝ → ℝ)
    (h_one : Hf 0 = 1)
    (h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u)
    (h_lim : Tendsto Hf (𝓝 0) (𝓝 1)) :
    Continuous Hf := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  have h_sum :
      Tendsto (fun u => Hf (t + u) + Hf (t - u)) (𝓝 0) (𝓝 (2 * Hf t)) := by
    have h_prod :
        Tendsto (fun u => (2 * Hf t) * Hf u) (𝓝 0) (𝓝 ((2 * Hf t) * 1)) :=
      tendsto_const_nhds.mul h_lim
    have h_prod' :
        Tendsto (fun u => 2 * Hf t * Hf u) (𝓝 0) (𝓝 (2 * Hf t)) := by
      simpa [mul_assoc] using h_prod
    have h_eq :
        (fun u => Hf (t + u) + Hf (t - u)) = fun u => 2 * Hf t * Hf u := by
      funext u; exact h_dAlembert t u
    simpa [h_eq] using h_prod'
  have h_diff_sq :
      Tendsto (fun u => (Hf (t + u) - Hf (t - u)) ^ 2) (𝓝 0) (𝓝 (0 : ℝ)) := by
    have h_u_sq : Tendsto (fun u => (Hf u) ^ 2) (𝓝 0) (𝓝 ((1 : ℝ) ^ 2)) := by
      simpa [pow_two] using h_lim.mul h_lim
    have h_u_sq_sub : Tendsto (fun u => (Hf u) ^ 2 - 1) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using h_u_sq.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝 0) (𝓝 1))
    have h_const :
        Tendsto (fun _ : ℝ => 4 * ((Hf t) ^ 2 - 1)) (𝓝 0)
          (𝓝 (4 * ((Hf t) ^ 2 - 1))) := tendsto_const_nhds
    have h_mul :
        Tendsto (fun u => (4 * ((Hf t) ^ 2 - 1)) * ((Hf u) ^ 2 - 1)) (𝓝 0)
          (𝓝 0) := by
      simpa using h_const.mul h_u_sq_sub
    have h_eq :
        (fun u => (Hf (t + u) - Hf (t - u)) ^ 2) =
          (fun u => 4 * ((Hf t) ^ 2 - 1) * ((Hf u) ^ 2 - 1)) := by
      funext u
      exact dAlembert_diff_square Hf h_one h_dAlembert t u
    simpa [h_eq] using h_mul
  have h_abs :
      Tendsto (fun u => |Hf (t + u) - Hf (t - u)|) (𝓝 0) (𝓝 (0 : ℝ)) := by
    have h_sqrt :
        Tendsto (fun u => Real.sqrt ((Hf (t + u) - Hf (t - u)) ^ 2)) (𝓝 0)
          (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp h_diff_sq
    simpa [Real.sqrt_sq_eq_abs] using h_sqrt
  have h_diff :
      Tendsto (fun u => Hf (t + u) - Hf (t - u)) (𝓝 0) (𝓝 (0 : ℝ)) :=
    (tendsto_zero_iff_abs_tendsto_zero
      (f := fun u => Hf (t + u) - Hf (t - u))).2 h_abs
  have h_sum_diff :
      Tendsto
        (fun u => (Hf (t + u) + Hf (t - u)) + (Hf (t + u) - Hf (t - u)))
        (𝓝 0) (𝓝 (2 * Hf t)) := by
    simpa using h_sum.add h_diff
  have h_twice : Tendsto (fun u => 2 * Hf (t + u)) (𝓝 0) (𝓝 (2 * Hf t)) := by
    have h_eq :
        (fun u => (Hf (t + u) + Hf (t - u)) + (Hf (t + u) - Hf (t - u))) =
          (fun u => Hf (t + u) + Hf (t + u)) := by
      funext u; ring
    simpa [h_eq, two_mul] using h_sum_diff
  have h_half :
      Tendsto (fun u => (2 * Hf (t + u)) / 2) (𝓝 0) (𝓝 ((2 * Hf t) / 2)) := by
    simpa [div_eq_mul_inv] using
      h_twice.mul (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝 0) (𝓝 _))
  have h_at0 : Tendsto (fun u => Hf (t + u)) (𝓝 0) (𝓝 (Hf t)) := by
    simpa using h_half
  have h_map :
      Tendsto Hf (map (fun u => t + u) (𝓝 0)) (𝓝 (Hf t)) :=
    (tendsto_map'_iff).2 h_at0
  have h_tendsto : Tendsto Hf (𝓝 t) (𝓝 (Hf t)) := by
    simpa [map_add_left_nhds_zero] using h_map
  exact h_tendsto

/-- Transport continuous `G F` on `ℝ` to `ContinuousOn F (Ioi 0)`. -/
theorem continuousOn_of_continuous_G
    (F : ℝ → ℝ) (hG : Continuous (G F)) :
    ContinuousOn F (Set.Ioi 0) := by
  intro x hx
  have hxpos : 0 < x := hx
  have hlog : ContinuousWithinAt Real.log (Set.Ioi 0) x :=
    (Real.continuousAt_log (ne_of_gt hxpos)).continuousWithinAt
  have hcomp : ContinuousWithinAt (G F ∘ Real.log) (Set.Ioi 0) x :=
    hG.continuousAt.comp_continuousWithinAt hlog
  have heq : EqOn F (G F ∘ Real.log) (Set.Ioi 0) := by
    intro y hy
    simp [Function.comp_apply, G, Real.exp_log hy]
  exact ContinuousWithinAt.congr hcomp heq (by simp [G, Real.exp_log hxpos])

/-! ## The ladder, first stated conditionally

The shrink was assembled in two stages: this conditional form, and then the bridge
`Tendsto (H F) (𝓝 0) (𝓝 1)` that discharges its hypothesis. Both are kept, because
the conditional form is the reusable half. -/

/-- Continuity on the positives, given the tendsto bridge as an explicit hypothesis.
The hypothesis is **not** a kernel member; it is discharged below by
`composition_calibration_tendsto_H_one`. -/
theorem composition_calibration_forces_continuity_of_tendsto
    (F : ℝ → ℝ)
    (hComp : SatisfiesCompositionLaw F)
    (hCalib : IsCalibrated F)
    (hLim : Tendsto (H F) (𝓝 0) (𝓝 1)) :
    ContinuousOn F (Set.Ioi 0) := by
  have ⟨h_H0, h_dAlembert⟩ := composition_calibration_dAlembert F hComp hCalib
  have hHcont := dAlembert_continuous_of_tendsto_at_zero (H F) h_H0 h_dAlembert hLim
  have hGcont : Continuous (G F) := by
    have : G F = fun t => H F t - 1 := by
      funext t; simp [H]
    rw [this]
    exact hHcont.sub continuous_const
  exact continuousOn_of_continuous_G F hGcont

/-- The unconditional shrink as a proposition, so the reduction below can be stated
as an equivalence. -/
def composition_calibration_forces_continuity_goal (F : ℝ → ℝ) : Prop :=
  SatisfiesCompositionLaw F → IsCalibrated F → ContinuousOn F (Set.Ioi 0)

/-- Reduction: the shrink is **equivalent** to the tendsto bridge. Proved before the
bridge was closed, and worth keeping: it says the bridge was not a convenient
sufficient condition but the exact content of the shrink, so no weaker limit
statement would have done. -/
theorem composition_calibration_forces_continuity_goal_iff_tendsto (F : ℝ → ℝ) :
    composition_calibration_forces_continuity_goal F ↔
      (SatisfiesCompositionLaw F → IsCalibrated F → Tendsto (H F) (𝓝 0) (𝓝 1)) := by
  constructor
  · intro hCont hComp hCalib
    -- From continuity of F on Ioi we get continuity of G, hence tendsto of H at 0.
    have hG : Continuous (G F) := by
      have hOn := hCont hComp hCalib
      have h := ContinuousOn.comp_continuous hOn Real.continuous_exp
        (fun t => Set.mem_Ioi.mpr (Real.exp_pos t))
      simpa [G] using h
    have ⟨h_H0, _⟩ := composition_calibration_dAlembert F hComp hCalib
    have hHcont : Continuous (H F) := by
      have : H F = fun t => G F t + 1 := rfl
      rw [this]
      exact hG.add continuous_const
    have htend0 := hHcont.tendsto 0
    rwa [h_H0] at htend0
  · intro hTend hComp hCalib
    exact composition_calibration_forces_continuity_of_tendsto F hComp hCalib
      (hTend hComp hCalib)

/-! ## Closing the bridge

Everything from here discharges `Tendsto (H F) (𝓝 0) (𝓝 1)` from the composition law
and calibration alone. -/

/-- The first log-derivative vanishes at the origin. Calibration makes `deriv (G F)`
genuinely differentiable at `0`, hence continuous there, and the limit is `0` by
oddness, so the value must be `0` too. -/
theorem calibrated_deriv_G_zero
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    deriv (G F) 0 = 0 := by
  have hzero : Tendsto (deriv (G F)) (𝓝 0) (𝓝 0) := by
    have h := calibrated_tendsto_deriv_H_zero F hComp hCalib
    rwa [deriv_H_eq_deriv_G F] at h
  have hcont : Tendsto (deriv (G F)) (𝓝 0) (𝓝 (deriv (G F) 0)) :=
    (calibrated_hasDerivAt_deriv F hCalib).continuousAt.tendsto
  exact tendsto_nhds_unique hcont hzero

/-- On a right window the derivative is positive, because `deriv (G F) t / t → 1`
and `t > 0`. This is the quantitative form of Step 1: not merely nonzero, but
signed. -/
theorem calibrated_deriv_pos_right
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    ∃ ε > 0, ∀ t : ℝ, 0 < t → t < ε → 0 < deriv (G F) t := by
  have h0 : deriv (G F) 0 = 0 := calibrated_deriv_G_zero F hComp hCalib
  have hder := calibrated_hasDerivAt_deriv F hCalib
  have hslope := (hasDerivAt_iff_tendsto_slope).1 hder
  have hnhds :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ), |slope (deriv (G F)) 0 t - 1| < (1 / 2 : ℝ) := by
    have := Metric.tendsto_nhds.1 hslope (1 / 2 : ℝ) (by norm_num)
    simpa [Real.dist_eq] using this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hnhds
  obtain ⟨ε, hε, hball⟩ := hnhds
  refine ⟨ε, hε, fun t ht htlt => ?_⟩
  have htne : t ≠ 0 := ne_of_gt ht
  have hd : dist t (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]; exact htlt
  have hs : |slope (deriv (G F)) 0 t - 1| < (1 / 2 : ℝ) := hball hd htne
  have hq : |deriv (G F) t / t - 1| < (1 / 2 : ℝ) := by
    simpa [slope_def_field, h0] using hs
  have hq' : (0 : ℝ) < deriv (G F) t / t := by
    have := abs_lt.1 hq
    linarith [this.1]
  have hkey : deriv (G F) t / t * t = deriv (G F) t := div_mul_cancel₀ _ htne
  have hmul := mul_pos hq' ht
  rwa [hkey] at hmul

/-- Strict monotonicity on a right window, from positive derivative plus the
punctured differentiability that supplies continuity there. -/
theorem calibrated_strictMonoOn_right
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    ∃ ε > 0, StrictMonoOn (G F) (Set.Ioo 0 ε) := by
  obtain ⟨ε₁, hε₁, hpos⟩ := calibrated_deriv_pos_right F hComp hCalib
  obtain ⟨ε₂, hε₂, hdiff⟩ := calibrated_differentiable_punctured F hCalib
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  have hcont : ContinuousOn (G F) (Set.Ioo 0 (min ε₁ ε₂)) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have htlt : |t| < ε₂ := by
      rw [abs_of_pos ht.1]
      exact lt_of_lt_of_le ht.2 (min_le_right _ _)
    exact ((hdiff t ht0 htlt).continuousAt).continuousWithinAt
  refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont ?_
  intro t ht
  rw [interior_Ioo] at ht
  exact hpos t ht.1 (lt_of_lt_of_le ht.2 (min_le_left _ _))

/-- **A d'Alembert solution bounds itself below**, with no regularity at all:
`H (2t) + 1 = 2 (H t)²` at `t = s/2` gives `H s ≥ -1` everywhere. This is the step
that makes the monotone-limit argument free of any mean-value estimate. -/
theorem dAlembert_ge_neg_one
    (Hf : ℝ → ℝ) (h_one : Hf 0 = 1)
    (h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u) (s : ℝ) :
    -1 ≤ Hf s := by
  have h := h_dAlembert (s / 2) (s / 2)
  rw [show s / 2 + s / 2 = s by ring, sub_self, h_one] at h
  nlinarith [sq_nonneg (Hf (s / 2))]

/-- The one-sided limit exists: monotone on a right window, bounded below globally. -/
theorem calibrated_tendsto_G_right
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    ∃ L : ℝ, Tendsto (G F) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨ε, hε, hmono⟩ := calibrated_strictMonoOn_right F hComp hCalib
  obtain ⟨h_H0, h_dA⟩ := composition_calibration_dAlembert F hComp hCalib
  have hbdd : BddBelow (G F '' Set.Ioo 0 ε) := by
    refine ⟨-2, ?_⟩
    rintro y ⟨t, -, rfl⟩
    have hge : -1 ≤ G F t + 1 := dAlembert_ge_neg_one (H F) h_H0 h_dA t
    linarith
  exact ⟨sInf (G F '' Set.Ioo 0 ε),
    MonotoneOn.tendsto_nhdsWithin_Ioo_right (Set.nonempty_Ioo.mpr hε) hmono.monotoneOn hbdd⟩

/-- Positive dilations preserve the right-hand filter at the origin, so the limit can
be read off at `2t` and `3t` as well as at `t`. -/
private theorem tendsto_scale_right {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have h : Tendsto (fun t : ℝ => c * t) (𝓝 (0 : ℝ)) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

/-- **The limit value is forced to be one.** Two instances of the functional equation
do it: `(t, t)` gives `M + 1 = 2M²` and `(2t, t)` gives `2M = 2M²`, and subtracting
leaves `M = 1` with no case analysis.

One instance is not enough. `M + 1 = 2M²` alone admits `M = -1/2`, and the doubling
relation is satisfied at that value, so the second instance is doing real work rather
than confirming the first. -/
theorem calibrated_tendsto_H_one_right
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    Tendsto (H F) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  obtain ⟨L, hL⟩ := calibrated_tendsto_G_right F hComp hCalib
  obtain ⟨h_H0, h_dA⟩ := composition_calibration_dAlembert F hComp hCalib
  have hH : Tendsto (H F) (𝓝[>] (0 : ℝ)) (𝓝 (L + 1)) := by
    have hfun : (fun t : ℝ => G F t + 1) = H F := rfl
    rw [← hfun]
    exact hL.add tendsto_const_nhds
  have h2 : Tendsto (fun t : ℝ => H F (2 * t)) (𝓝[>] (0 : ℝ)) (𝓝 (L + 1)) :=
    hH.comp (tendsto_scale_right two_pos)
  have h3 : Tendsto (fun t : ℝ => H F (3 * t)) (𝓝[>] (0 : ℝ)) (𝓝 (L + 1)) :=
    hH.comp (tendsto_scale_right (by norm_num : (0 : ℝ) < 3))
  have hA : ∀ t : ℝ, H F (2 * t) + 1 = 2 * H F t * H F t := by
    intro t
    have h := h_dA t t
    rw [show t + t = 2 * t by ring, sub_self, h_H0] at h
    exact h
  have hB : ∀ t : ℝ, H F (3 * t) + H F t = 2 * H F (2 * t) * H F t := by
    intro t
    have h := h_dA (2 * t) t
    rw [show 2 * t + t = 3 * t by ring, show 2 * t - t = t by ring] at h
    exact h
  have hlimA : (L + 1) + 1 = 2 * (L + 1) * (L + 1) := by
    have hl : Tendsto (fun t : ℝ => H F (2 * t) + 1) (𝓝[>] (0 : ℝ))
        (𝓝 ((L + 1) + 1)) := h2.add tendsto_const_nhds
    have hr : Tendsto (fun t : ℝ => 2 * H F t * H F t) (𝓝[>] (0 : ℝ))
        (𝓝 (2 * (L + 1) * (L + 1))) :=
      (tendsto_const_nhds.mul hH).mul hH
    exact tendsto_nhds_unique (Filter.Tendsto.congr hA hl) hr
  have hlimB : (L + 1) + (L + 1) = 2 * (L + 1) * (L + 1) := by
    have hl : Tendsto (fun t : ℝ => H F (3 * t) + H F t) (𝓝[>] (0 : ℝ))
        (𝓝 ((L + 1) + (L + 1))) := h3.add hH
    have hr : Tendsto (fun t : ℝ => 2 * H F (2 * t) * H F t) (𝓝[>] (0 : ℝ))
        (𝓝 (2 * (L + 1) * (L + 1))) :=
      (tendsto_const_nhds.mul h2).mul hH
    exact tendsto_nhds_unique (Filter.Tendsto.congr hB hl) hr
  have hM : L + 1 = 1 := by linarith
  rwa [hM] at hH

/-- **The bridge.** The composition law plus calibration force `H F → 1` at the
origin, two-sided. Evenness carries the right-hand limit to the left, and the value
`H F 0 = 1` closes the puncture. -/
theorem composition_calibration_tendsto_H_one
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    Tendsto (H F) (𝓝 (0 : ℝ)) (𝓝 1) := by
  obtain ⟨h_H0, h_dA⟩ := composition_calibration_dAlembert F hComp hCalib
  have hright := calibrated_tendsto_H_one_right F hComp hCalib
  have heven : Function.Even (H F) := dAlembert_even (H F) h_H0 h_dA
  have hnegmap : Tendsto (fun t : ℝ => -t) (𝓝[<] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun t : ℝ => -t) (𝓝 (0 : ℝ)) (𝓝 (-0 : ℝ)) :=
        continuous_neg.tendsto 0
      rw [neg_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact neg_pos.mpr (Set.mem_Iio.mp ht)
  have hleft : Tendsto (H F) (𝓝[<] (0 : ℝ)) (𝓝 1) :=
    Filter.Tendsto.congr (fun t => heven t) (hright.comp hnegmap)
  have hpunct : Tendsto (H F) (𝓝[({(0 : ℝ)}ᶜ)] (0 : ℝ)) (𝓝 1) := by
    rw [← Iio_union_Ioi, nhdsWithin_union, Filter.tendsto_sup]
    exact ⟨hleft, hright⟩
  have hcw : ContinuousWithinAt (H F) ({(0 : ℝ)}ᶜ) 0 := by
    unfold ContinuousWithinAt
    rw [h_H0]
    exact hpunct
  have hca : ContinuousAt (H F) 0 := continuousWithinAt_compl_self.mp hcw
  have h := hca.tendsto
  rwa [h_H0] at h

/-- **The continuity shrink.** The composition law plus calibration force continuity
on the positives, so `ContinuousOn F (Set.Ioi 0)` is redundant as a kernel member and
was deleted from `RecognitionKernel` on 2026-07-25. -/
theorem composition_calibration_forces_continuity
    (F : ℝ → ℝ) (hComp : SatisfiesCompositionLaw F) (hCalib : IsCalibrated F) :
    ContinuousOn F (Set.Ioi 0) :=
  composition_calibration_forces_continuity_of_tendsto F hComp hCalib
    (composition_calibration_tendsto_H_one F hComp hCalib)

end
end KernelContinuity
end Foundation
end IndisputableMonolith

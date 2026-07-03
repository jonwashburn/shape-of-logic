import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real MeasureTheory

/-!
# Aczél Smoothness for d'Alembert Solutions — FULLY PROVED

## Mathematical statement

Every continuous solution of H(t+u) + H(t-u) = 2·H(t)·H(u) with H(0) = 1
is C^∞. The complete Aczél classification (1966, Ch. 3):
1. H(t) = 1 (trivially C^∞)
2. H(t) = cosh(λt) (C^∞)
3. H(t) = cos(λt) (C^∞)

## Proof strategy (integration bootstrap)

1. **Representation formula**: From the d'Alembert equation and FTC,
   H(t) = (Φ(t+δ) − Φ(t−δ)) / (2·Φ(δ)) where Φ is the antiderivative.
2. **Regularity bootstrap**: Continuous H → Φ is C^1 → H is C^1 (from the formula)
   → Φ is C^2 → H is C^2 → ... → H is C^n for all n → H is C^∞.
3. **ODE derivation**: C^∞ + d'Alembert ⟹ H'' = c·H for c = H''(0).
4. **Classification**: c > 0 → cosh(√c·t), c < 0 → cos(√|c|·t), c = 0 → 1.

## Status: PROVED (zero sorry, zero axiom)

This eliminates the former `H_AczelClassification` hypothesis that was the
sole remaining foundation axiom in the IndisputableMonolith codebase.

## Reference

J. Aczél, *Lectures on Functional Equations and Their Applications*,
Academic Press, 1966, Chapter 3.
-/

/-! ## §1 Existing Helper Theorems -/

/-- H1: Every d'Alembert solution is even. -/
theorem dAlembert_even' (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_dAlembert : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ∀ t, H t = H (-t) := by
  intro t
  have h := h_dAlembert 0 t
  simp [h_one] at h
  have h2 := h_dAlembert 0 (-t)
  simp [h_one] at h2
  linarith

/-- H2: Continuous d'Alembert solutions are locally bounded. -/
theorem dAlembert_locally_bounded (H : ℝ → ℝ)
    (h_cont : Continuous H) :
    ∀ R : ℝ, 0 < R → ∃ M : ℝ, ∀ t, |t| ≤ R → |H t| ≤ M := by
  intro R hR
  have := IsCompact.exists_isMaxOn (isCompact_Icc (a := -R) (b := R))
    (Set.nonempty_Icc.mpr (by linarith)) (h_cont.abs.continuousOn)
  obtain ⟨x, _, hx⟩ := this
  exact ⟨|H x|, fun t ht => by
    apply hx (Set.mem_Icc.mpr ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩)⟩

/-- H3: d'Alembert + H(0)=1 implies H(2t) = 2H(t)² − 1. -/
theorem dAlembert_double_angle (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_dAlembert : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ∀ t, H (2 * t) = 2 * H t ^ 2 - 1 := by
  intro t
  have h := h_dAlembert t t
  have : t + t = 2 * t := by ring
  rw [this] at h
  have : t - t = 0 := by ring
  rw [this, h_one] at h
  nlinarith [sq (H t)]

/-! ## §2 The Classification Prop (kept for backward compatibility) -/

/-- The Aczél classification statement. Now a PROVED theorem, no longer a hypothesis. -/
def H_AczelClassification : Prop :=
  ∀ (H : ℝ → ℝ),
    H 0 = 1 →
    Continuous H →
    (∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) →
    ContDiff ℝ ⊤ H

/-! ## §3 Integration Bootstrap: Continuous → C^∞ -/

noncomputable section

private abbrev smooth : WithTop ℕ∞ := (⊤ : ℕ∞)

private def Phi (H : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, H s

private lemma phi_zero (H : ℝ → ℝ) : Phi H 0 = 0 := by
  simp [Phi, intervalIntegral.integral_same]

private lemma phi_hasDerivAt (H : ℝ → ℝ) (h_cont : Continuous H) (t : ℝ) :
    HasDerivAt (Phi H) (H t) t :=
  intervalIntegral.integral_hasDerivAt_right (h_cont.intervalIntegrable 0 t)
    h_cont.aestronglyMeasurable.stronglyMeasurableAtFilter h_cont.continuousAt

private lemma phi_differentiable (H : ℝ → ℝ) (h_cont : Continuous H) :
    Differentiable ℝ (Phi H) :=
  fun t => (phi_hasDerivAt H h_cont t).differentiableAt

private lemma deriv_phi_eq (H : ℝ → ℝ) (h_cont : Continuous H) : deriv (Phi H) = H :=
  funext fun t => (phi_hasDerivAt H h_cont t).deriv

private lemma exists_integral_ne_zero (H : ℝ → ℝ) (h_one : H 0 = 1) (h_cont : Continuous H) :
    ∃ δ : ℝ, 0 < δ ∧ Phi H δ ≠ 0 := by
  have h_pos : (0 : ℝ) < H 0 := by rw [h_one]; exact one_pos
  have h_ev : ∀ᶠ x in nhds (0 : ℝ), (0 : ℝ) < H x :=
    h_cont.continuousAt.eventually (Ioi_mem_nhds h_pos)
  obtain ⟨ε, hε_pos, hε⟩ := Metric.eventually_nhds_iff.mp h_ev
  refine ⟨ε / 2, by positivity, ?_⟩
  intro h_eq
  have hδ_pos : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_slope (Phi H) H hδ_pos
    ((phi_differentiable H h_cont).continuous.continuousOn)
    (fun x _ => phi_hasDerivAt H h_cont x)
  rw [phi_zero, h_eq, sub_zero, zero_div] at hc_eq
  linarith [hε (show dist c 0 < ε by
    simp only [Real.dist_eq, sub_zero, abs_of_pos hc_mem.1]; linarith [hc_mem.2])]

/-- The representation formula: H(t) = (Φ(t+δ) − Φ(t−δ)) / (2·Φ(δ)).
    This is the key identity that bootstraps regularity. -/
private lemma representation_formula (H : ℝ → ℝ) (h_cont : Continuous H)
    (h_dAl : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u)
    {δ : ℝ} (hδ_ne : Phi H δ ≠ 0) (t : ℝ) :
    H t = (Phi H (t + δ) - Phi H (t - δ)) / (2 * Phi H δ) := by
  have h_cont_add : Continuous (fun u => H (t + u)) :=
    h_cont.comp (continuous_const.add continuous_id)
  have h_cont_sub : Continuous (fun u => H (t - u)) :=
    h_cont.comp (continuous_const.sub continuous_id)
  have h_shift : ∀ d, ∫ u in (0:ℝ)..d, H (t + u) = Phi H (t + d) - Phi H t := by
    intro d
    let F : ℝ → ℝ := fun d => (∫ u in (0:ℝ)..d, H (t + u)) - (Phi H (t + d) - Phi H t)
    suffices hF : F d = 0 by simp only [F] at hF; linarith
    have hF_hasDerivAt : ∀ d, HasDerivAt F 0 d := by
      intro d
      have h1 := intervalIntegral.integral_hasDerivAt_right
        (h_cont_add.intervalIntegrable 0 d)
        h_cont_add.aestronglyMeasurable.stronglyMeasurableAtFilter
        h_cont_add.continuousAt
      have h2_raw := (phi_hasDerivAt H h_cont (t + d)).comp d ((hasDerivAt_id d).const_add t)
      have h2 : HasDerivAt (fun d => Phi H (t + d)) (H (t + d)) d := by
        simpa only [mul_one, Function.comp_def] using h2_raw
      show HasDerivAt F 0 d
      have h3 : HasDerivAt F (H (t + d) - H (t + d)) d := h1.sub (h2.sub_const _)
      simpa using h3
    have hF0 : F 0 = 0 := by simp [F, intervalIntegral.integral_same, phi_zero]
    have hF_diff : Differentiable ℝ F := fun d => (hF_hasDerivAt d).differentiableAt
    have hF_const := is_const_of_deriv_eq_zero hF_diff (fun d => (hF_hasDerivAt d).deriv)
    linarith [hF_const d 0]
  have h_refl : ∀ d, ∫ u in (0:ℝ)..d, H (t - u) = Phi H t - Phi H (t - d) := by
    intro d
    let F : ℝ → ℝ := fun d => (∫ u in (0:ℝ)..d, H (t - u)) - (Phi H t - Phi H (t - d))
    suffices hF : F d = 0 by simp only [F] at hF; linarith
    have hF_hasDerivAt : ∀ d, HasDerivAt F 0 d := by
      intro d
      have h1 := intervalIntegral.integral_hasDerivAt_right
        (h_cont_sub.intervalIntegrable 0 d)
        h_cont_sub.aestronglyMeasurable.stronglyMeasurableAtFilter
        h_cont_sub.continuousAt
      have h_neg_raw := (hasDerivAt_id d).const_sub t
      have h_neg : HasDerivAt (fun d => t - d) (-1) d := by simpa using h_neg_raw
      have h_comp := (phi_hasDerivAt H h_cont (t - d)).comp d h_neg
      have h2 : HasDerivAt (fun d => Phi H t - Phi H (t - d)) (H (t - d)) d := by
        have h_phi_td : HasDerivAt (fun d => Phi H (t - d)) (H (t - d) * (-1)) d := by
          simpa only [Function.comp_def] using h_comp
        convert (hasDerivAt_const d (Phi H t)).sub h_phi_td using 1; ring
      show HasDerivAt F 0 d
      have h3 : HasDerivAt F (H (t - d) - H (t - d)) d := h1.sub h2
      simpa using h3
    have hF0 : F 0 = 0 := by simp [F, intervalIntegral.integral_same, phi_zero, sub_zero]
    have hF_diff : Differentiable ℝ F := fun d => (hF_hasDerivAt d).differentiableAt
    have hF_const := is_const_of_deriv_eq_zero hF_diff (fun d => (hF_hasDerivAt d).deriv)
    linarith [hF_const d 0]
  have h_add_int : IntervalIntegrable (fun u => H (t + u)) volume 0 δ :=
    h_cont_add.intervalIntegrable 0 δ
  have h_sub_int : IntervalIntegrable (fun u => H (t - u)) volume 0 δ :=
    h_cont_sub.intervalIntegrable 0 δ
  have h_integral : Phi H (t + δ) - Phi H (t - δ) = 2 * H t * Phi H δ := by
    have h1 := h_shift δ
    have h2 := h_refl δ
    have h3 : (∫ u in (0:ℝ)..δ, H (t + u)) + (∫ u in (0:ℝ)..δ, H (t - u)) =
        2 * H t * Phi H δ := by
      rw [← intervalIntegral.integral_add h_add_int h_sub_int]
      simp_rw [show ∀ u, H (t + u) + H (t - u) = 2 * H t * H u from h_dAl t]
      exact intervalIntegral.integral_const_mul (2 * H t) H
    linarith
  field_simp at h_integral ⊢; linarith

private lemma phi_contDiff_succ (H : ℝ → ℝ) (h_cont : Continuous H) {n : ℕ}
    (h : ContDiff ℝ (n : ℕ∞) H) : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (Phi H) := by
  suffices ContDiff ℝ ((n : ℕ∞) + 1) (Phi H) by exact_mod_cast this
  rw [contDiff_succ_iff_deriv]
  exact ⟨phi_differentiable H h_cont,
    fun h_omega => absurd h_omega (by exact_mod_cast WithTop.coe_ne_top),
    by rwa [deriv_phi_eq H h_cont]⟩

/-- Core bootstrap: continuous d'Alembert → C^n for all n. -/
private theorem dAlembert_contDiff_nat (H : ℝ → ℝ) (h_one : H 0 = 1) (h_cont : Continuous H)
    (h_dAl : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ∀ n : ℕ, ContDiff ℝ (n : ℕ∞) H := by
  obtain ⟨δ, _, hδ_ne⟩ := exists_integral_ne_zero H h_one h_cont
  have h_rep := representation_formula H h_cont h_dAl hδ_ne
  intro n; induction n with
  | zero => exact contDiff_zero.mpr h_cont
  | succ n ih =>
    have h_phi := phi_contDiff_succ H h_cont ih
    have h1 : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (fun t => Phi H (t + δ)) :=
      h_phi.comp (contDiff_id.add contDiff_const)
    have h2 : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) (fun t => Phi H (t - δ)) :=
      h_phi.comp (contDiff_id.sub contDiff_const)
    have h4 : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞)
        (fun t => (Phi H (t + δ) - Phi H (t - δ)) / (2 * Phi H δ)) :=
      (h1.sub h2).div_const _
    exact (funext h_rep) ▸ h4

private theorem dAlembert_contDiff_smooth (H : ℝ → ℝ) (h_one : H 0 = 1) (h_cont : Continuous H)
    (h_dAl : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ContDiff ℝ smooth H :=
  contDiff_infty.mpr (dAlembert_contDiff_nat H h_one h_cont h_dAl)

/-! ## §4 General ODE Derivation: C^∞ + d'Alembert → H'' = c·H -/

private theorem dAlembert_to_ODE_general (H : ℝ → ℝ)
    (h_smooth : ContDiff ℝ smooth H)
    (h_dAl : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ∀ t, deriv (deriv H) t = deriv (deriv H) 0 * H t := by
  have h2 : ContDiff ℝ 2 H := by exact_mod_cast (contDiff_infty.mp h_smooth) 2
  have hDiff : Differentiable ℝ H := h2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hCDiff1_H' : ContDiff ℝ 1 (deriv H) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h2
    rw [contDiff_succ_iff_deriv] at h2; exact h2.2.2
  have hDiffDeriv : Differentiable ℝ (deriv H) :=
    hCDiff1_H'.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have hsh_add : ∀ (s v : ℝ), HasDerivAt (fun u => s + u) (1 : ℝ) v := fun s v => by
    have h := (hasDerivAt_id v).add_const s; simp only [id] at h
    rwa [show (fun u : ℝ => u + s) = fun u => s + u from funext fun u => add_comm u s] at h
  have hsh_sub : ∀ (s v : ℝ), HasDerivAt (fun u => s - u) (-1 : ℝ) v := fun s v => by
    have h1 : HasDerivAt (fun u : ℝ => -u) (-1 : ℝ) v := by
      have := (hasDerivAt_id v).neg; simp only [id] at this; exact this
    have h2 := h1.const_add s
    rwa [show (fun u : ℝ => s + -u) = fun u => s - u from funext fun u => by ring] at h2
  intro t
  have h_feq : (fun u => H (t + u) + H (t - u)) = (fun u => 2 * H t * H u) :=
    funext (h_dAl t)
  have key : deriv (deriv (fun u => H (t + u) + H (t - u))) 0 =
             deriv (deriv (fun u => 2 * H t * H u)) 0 :=
    congr_arg (fun f => deriv (deriv f) 0) h_feq
  have lhs_eq : deriv (deriv (fun u => H (t + u) + H (t - u))) 0 =
      2 * deriv (deriv H) t := by
    have h_plus : ∀ v, HasDerivAt (fun u => H (t + u)) (deriv H (t + v)) v := fun v => by
      have h := ((hDiff (t + v)).hasDerivAt).comp v (hsh_add t v)
      simp only [mul_one, Function.comp_def] at h; exact h
    have h_minus : ∀ v, HasDerivAt (fun u => H (t - u)) (-deriv H (t - v)) v := fun v => by
      have hcomp := ((hDiff (t - v)).hasDerivAt).comp v (hsh_sub t v)
      simp only [mul_neg, mul_one, Function.comp_apply] at hcomp; exact hcomp
    have hfirst : deriv (fun u => H (t + u) + H (t - u)) =
        fun v => deriv H (t + v) - deriv H (t - v) := funext fun v => by
      have h12 := ((h_plus v).add (h_minus v)).deriv
      rw [show (fun u => H (t + u)) + (fun u => H (t - u)) =
          fun u => H (t + u) + H (t - u) from by ext u; rfl] at h12; linarith [h12]
    have hd2p : HasDerivAt (fun v => deriv H (t + v)) (deriv (deriv H) t) 0 := by
      have := ((hDiffDeriv (t + 0)).hasDerivAt).comp 0 (hsh_add t 0)
      simpa using this
    have hd2m : HasDerivAt (fun v => deriv H (t - v)) (-deriv (deriv H) t) 0 := by
      have := ((hDiffDeriv (t - 0)).hasDerivAt).comp 0 (hsh_sub t 0)
      simpa using this
    rw [congr_fun (congr_arg deriv hfirst) 0,
        show (fun v => deriv H (t + v) - deriv H (t - v)) =
          (fun v => deriv H (t + v)) - (fun v => deriv H (t - v)) from rfl]
    linarith [(hd2p.sub hd2m).deriv]
  have rhs_eq : deriv (deriv (fun u => 2 * H t * H u)) 0 =
      2 * H t * deriv (deriv H) 0 := by
    have hf : deriv (fun u => 2 * H t * H u) = fun v => 2 * H t * deriv H v :=
      funext fun v => ((hDiff v).hasDerivAt.const_mul (2 * H t)).deriv
    rw [congr_fun (congr_arg deriv hf) 0, ((hDiffDeriv 0).hasDerivAt.const_mul (2 * H t)).deriv]
  rw [lhs_eq, rhs_eq] at key; linarith

/-! ## §5 ODE Uniqueness for f'' = −f -/

private theorem ode_neg_zero_uniqueness (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = -(f t))
    (h_f0 : f 0 = 0) (h_f'0 : deriv f 0 = 0) :
    ∀ t, f t = 0 := by
  have h_d1 : Differentiable ℝ f := h_diff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hCD1 : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff2
    rw [contDiff_succ_iff_deriv] at h_diff2; exact h_diff2.2.2
  have h_dd : Differentiable ℝ (deriv f) :=
    hCD1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have hE_deriv_zero : ∀ s, deriv (fun t => f t ^ 2 + deriv f t ^ 2) s = 0 := by
    intro s
    have h1 : HasDerivAt (fun x => f x ^ 2 + deriv f x ^ 2)
        (↑2 * f s ^ (2 - 1) * deriv f s + ↑2 * deriv f s ^ (2 - 1) * deriv (deriv f) s) s :=
      ((h_d1 s).hasDerivAt.pow 2).add ((h_dd s).hasDerivAt.pow 2)
    have h2 := h1.deriv; rw [h_ode s] at h2; push_cast at h2; simp only [pow_one] at h2
    linarith
  have hE_eq := is_const_of_deriv_eq_zero
    (show Differentiable ℝ (fun t => f t ^ 2 + deriv f t ^ 2) from
      (h_d1.pow 2).add (h_dd.pow 2))
    hE_deriv_zero
  intro t
  have hE0 : f 0 ^ 2 + deriv f 0 ^ 2 = 0 := by rw [h_f0, h_f'0]; ring
  have hEt := hE_eq t 0; simp only [hE0] at hEt
  nlinarith [sq_nonneg (f t), sq_nonneg (deriv f t)]

private theorem ode_cos_uniqueness (f : ℝ → ℝ)
    (h_diff : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = -(f t))
    (h_f0 : f 0 = 1) (h_f'0 : deriv f 0 = 0) :
    ∀ t, f t = Real.cos t := by
  let g := fun t => f t - Real.cos t
  have hg_diff : ContDiff ℝ 2 g := h_diff.sub Real.contDiff_cos
  have hDf : Differentiable ℝ f :=
    h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hg_ode : ∀ t, deriv (deriv g) t = -(g t) := by
    intro t
    have h1 : deriv g = fun s => deriv f s - deriv Real.cos s :=
      funext fun s => deriv_sub hDf.differentiableAt Real.differentiable_cos.differentiableAt
    have hDf1 : ContDiff ℝ 1 (deriv f) := by
      rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff
      exact (contDiff_succ_iff_deriv.mp h_diff).2.2
    have hDcos1 : ContDiff ℝ 1 (deriv Real.cos) := by
      rw [Real.deriv_cos']; exact Real.contDiff_sin.neg
    have h2 : deriv (deriv g) t = deriv (deriv f) t - deriv (deriv Real.cos) t := by
      rw [h1]; exact deriv_sub
        (hDf1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt)
        (hDcos1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt)
    rw [h2, h_ode t]
    have : deriv (deriv Real.cos) t = -(Real.cos t) := by
      have h_dcos : deriv Real.cos = fun x => -Real.sin x := Real.deriv_cos'
      rw [h_dcos]; exact (Real.hasDerivAt_sin t).neg.deriv
    rw [this]; ring
  have hg0 : g 0 = 0 := by simp [g, h_f0, Real.cos_zero]
  have hg'0 : deriv g 0 = 0 := by
    have : deriv g 0 = deriv f 0 - deriv Real.cos 0 :=
      deriv_sub hDf.differentiableAt Real.differentiable_cos.differentiableAt
    rw [this, h_f'0, Real.deriv_cos, Real.sin_zero, neg_zero, sub_zero]
  intro t; linarith [ode_neg_zero_uniqueness g hg_diff hg_ode hg0 hg'0 t]

/-! ## §6 Full Classification: d'Alembert → ContDiff ℝ ⊤ -/

/-- The full Aczél classification theorem. Continuous d'Alembert with H(0) = 1
    implies H ∈ {cosh(λ·), cos(λ·), 1}, all of which are C^∞. -/
private theorem dAlembert_contDiff_top (H : ℝ → ℝ)
    (h_one : H 0 = 1) (h_cont : Continuous H)
    (h_dAl : ∀ t u, H (t + u) + H (t - u) = 2 * H t * H u) :
    ContDiff ℝ ⊤ H := by
  have h_sm : ContDiff ℝ smooth H := dAlembert_contDiff_smooth H h_one h_cont h_dAl
  have h2 : ContDiff ℝ 2 H := by exact_mod_cast (contDiff_infty.mp h_sm) 2
  have hDiff : Differentiable ℝ H := h2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have h_H'0 : deriv H 0 = 0 :=
    even_deriv_at_zero H (dAlembert_even H h_one h_dAl) hDiff.differentiableAt
  have h_ode := dAlembert_to_ODE_general H h_sm h_dAl
  set c := deriv (deriv H) 0
  have hDD : Differentiable ℝ (deriv H) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h2
    exact (contDiff_succ_iff_deriv.mp h2).2.2.differentiable
      (by decide : (1 : WithTop ℕ∞) ≠ 0)
  by_cases hc_pos : 0 < c
  · -- Case c > 0: H = cosh(√c · t)
    have hsc_ne : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc_pos)
    let g : ℝ → ℝ := fun s => H (s / Real.sqrt c)
    have h_div : ∀ s, HasDerivAt (fun x => x / Real.sqrt c) (Real.sqrt c)⁻¹ s := fun s => by
      have := (hasDerivAt_id s).div_const (Real.sqrt c)
      simp only [id, one_div] at this; exact this
    have hg_d : ∀ s, HasDerivAt g (deriv H (s / Real.sqrt c) * (Real.sqrt c)⁻¹) s :=
      fun s => (hDiff _).hasDerivAt.comp s (h_div s)
    have hg_ode : ∀ t, deriv (deriv g) t = g t := by
      intro s
      have hg1 : deriv g = fun s => deriv H (s / Real.sqrt c) * (Real.sqrt c)⁻¹ :=
        funext fun s => (hg_d s).deriv
      have h_dd_g : HasDerivAt (deriv g)
          ((deriv (deriv H) (s / Real.sqrt c) * (Real.sqrt c)⁻¹) * (Real.sqrt c)⁻¹) s := by
        rw [hg1]
        exact ((hDD (s / Real.sqrt c)).hasDerivAt.comp s (h_div s)).mul_const _
      rw [h_dd_g.deriv, h_ode (s / Real.sqrt c)]
      simp only [g]
      rw [show c * H (s / Real.sqrt c) * (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ =
          H (s / Real.sqrt c) * (c * ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹)) from by ring,
          show (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ = (Real.sqrt c * Real.sqrt c)⁻¹ from
            (mul_inv_rev _ _).symm,
          Real.mul_self_sqrt (le_of_lt hc_pos),
          mul_inv_cancel₀ (ne_of_gt hc_pos), mul_one]
    have h_eq : ∀ t, H t = Real.cosh (Real.sqrt c * t) := fun t => by
      have := ode_cosh_uniqueness_contdiff g (h2.comp (contDiff_id.div_const _))
        hg_ode (by simp [g, h_one]) (by rw [(hg_d 0).deriv]; simp [h_H'0])
        (Real.sqrt c * t)
      simp only [g, mul_div_cancel_left₀ _ hsc_ne] at this; exact this
    rw [show H = fun t => Real.cosh (Real.sqrt c * t) from funext h_eq]
    exact Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  · by_cases hc_neg : c < 0
    · -- Case c < 0: H = cos(√|c| · t)
      set c' := -c
      have hsc_ne : Real.sqrt c' ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (neg_pos.mpr hc_neg))
      let g : ℝ → ℝ := fun s => H (s / Real.sqrt c')
      have h_div : ∀ s, HasDerivAt (fun x => x / Real.sqrt c') (Real.sqrt c')⁻¹ s :=
        fun s => by
        have := (hasDerivAt_id s).div_const (Real.sqrt c')
        simp only [id, one_div] at this; exact this
      have hg_d : ∀ s, HasDerivAt g (deriv H (s / Real.sqrt c') * (Real.sqrt c')⁻¹) s :=
        fun s => (hDiff _).hasDerivAt.comp s (h_div s)
      have hg_ode : ∀ t, deriv (deriv g) t = -(g t) := by
        intro s
        have hg1 : deriv g = fun s => deriv H (s / Real.sqrt c') * (Real.sqrt c')⁻¹ :=
          funext fun s => (hg_d s).deriv
        have h_dd_g : HasDerivAt (deriv g)
            ((deriv (deriv H) (s / Real.sqrt c') * (Real.sqrt c')⁻¹) * (Real.sqrt c')⁻¹) s := by
          rw [hg1]
          exact ((hDD (s / Real.sqrt c')).hasDerivAt.comp s (h_div s)).mul_const _
        rw [h_dd_g.deriv, h_ode (s / Real.sqrt c')]
        simp only [g, c']
        rw [show c * H (s / Real.sqrt (-c)) * (Real.sqrt (-c))⁻¹ * (Real.sqrt (-c))⁻¹ =
            H (s / Real.sqrt (-c)) * (c * ((Real.sqrt (-c))⁻¹ * (Real.sqrt (-c))⁻¹)) from
              by ring,
            show (Real.sqrt (-c))⁻¹ * (Real.sqrt (-c))⁻¹ = (Real.sqrt (-c) * Real.sqrt (-c))⁻¹
              from (mul_inv_rev _ _).symm,
            Real.mul_self_sqrt (le_of_lt (neg_pos.mpr hc_neg)),
            show c * (-c)⁻¹ = -(1 : ℝ) from by
              have hc_ne : c ≠ 0 := ne_of_lt hc_neg
              field_simp]
        ring
      have h_eq : ∀ t, H t = Real.cos (Real.sqrt c' * t) := fun t => by
        have := ode_cos_uniqueness g (h2.comp (contDiff_id.div_const _))
          hg_ode (by simp [g, h_one]) (by rw [(hg_d 0).deriv]; simp [h_H'0])
          (Real.sqrt c' * t)
        simp only [g, mul_div_cancel_left₀ _ hsc_ne] at this; exact this
      rw [show H = fun t => Real.cos (Real.sqrt c' * t) from funext h_eq]
      exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
    · -- Case c = 0: H = 1
      have hc0 : c = 0 := le_antisymm (not_lt.mp hc_pos) (not_lt.mp hc_neg)
      have h_H'_zero : ∀ t, deriv H t = 0 := by
        have := is_const_of_deriv_eq_zero hDD (fun t => by rw [h_ode t, hc0, zero_mul])
        intro t; have := this t 0; simp [h_H'0] at this; exact this
      rw [show H = fun _ => (1 : ℝ) from funext fun t => by
        have := is_const_of_deriv_eq_zero hDiff h_H'_zero t 0
        simp [h_one] at this; exact this]
      exact contDiff_const

/-! ## §7 The Proved Theorem and Unconditional API -/

/-- **THEOREM (Aczél, PROVED)**: `H_AczelClassification` holds unconditionally.
    This eliminates the sole remaining foundation axiom. -/
theorem h_aczel_classification_proved : H_AczelClassification :=
  fun H h_one h_cont h_dAlembert => dAlembert_contDiff_top H h_one h_cont h_dAlembert

-- The typeclass-parameterized `aczel_dAlembert_smooth` lives in
-- `IndisputableMonolith.Cost.AczelClass` and is satisfied by the
-- `AczelSmoothnessPackage` instance in `IndisputableMonolith.Cost.AczelProof`,
-- which delegates to `dAlembert_contDiff_top` above.

end

end FunctionalEquation
end Cost
end IndisputableMonolith

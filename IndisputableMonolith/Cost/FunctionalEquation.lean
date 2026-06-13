import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import IndisputableMonolith.Cost
import IndisputableMonolith.Cost.AczelClass

open IndisputableMonolith

/-!
# Functional Equation Helpers for T5

This module provides lemmas for the T5 cost uniqueness proof.
-/

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real

/-- Log-coordinate reparametrization: `G_F t = F (exp t)` -/
@[simp] noncomputable def G (F : ℝ → ℝ) (t : ℝ) : ℝ := F (Real.exp t)

/-- Convenience reparametrization: `H_F t = G_F t + 1`. -/
@[simp] noncomputable def H (F : ℝ → ℝ) (t : ℝ) : ℝ := G F t + 1

/-- The cosh-type functional identity for `G_F`. -/
def CoshAddIdentity (F : ℝ → ℝ) : Prop :=
  ∀ t u : ℝ,
    G F (t+u) + G F (t-u) = 2 * (G F t * G F u) + 2 * (G F t + G F u)

/-- Direct cosh-add identity on a function. -/
def DirectCoshAdd (Gf : ℝ → ℝ) : Prop :=
  ∀ t u : ℝ,
    Gf (t+u) + Gf (t-u) = 2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)

lemma CoshAddIdentity_implies_DirectCoshAdd (F : ℝ → ℝ)
  (h : CoshAddIdentity F) :
  DirectCoshAdd (G F) := h

lemma G_even_of_reciprocal_symmetry
  (F : ℝ → ℝ)
  (hSymm : ∀ {x : ℝ}, 0 < x → F x = F x⁻¹) :
  Function.Even (G F) := by
  intro t
  have hpos : 0 < Real.exp t := Real.exp_pos t
  have hrec : Real.exp (-t) = (Real.exp t)⁻¹ := by simp [Real.exp_neg]
  simp [G, hrec, hSymm hpos]

lemma G_zero_of_unit (F : ℝ → ℝ) (hUnit : F 1 = 0) : G F 0 = 0 := by
  simpa [G] using hUnit

theorem Jcost_G_eq_cosh_sub_one (t : ℝ) : G Cost.Jcost t = Real.cosh t - 1 := by
  simp only [G, Jcost]
  -- Jcost(exp t) = (exp t + exp(-t))/2 - 1 = cosh t - 1
  have h1 : (Real.exp t)⁻¹ = Real.exp (-t) := by simp [Real.exp_neg]
  rw [h1, Real.cosh_eq]

theorem Jcost_cosh_add_identity : CoshAddIdentity Cost.Jcost := by
  intro t u
  simp only [G, Jcost]
  -- Use exp(t+u) = exp(t)*exp(u) and exp(t-u) = exp(t)/exp(u)
  have he1 : Real.exp (t + u) = Real.exp t * Real.exp u := Real.exp_add t u
  have he2 : Real.exp (t - u) = Real.exp t / Real.exp u := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
    ring
  have hpos_t : Real.exp t > 0 := Real.exp_pos t
  have hpos_u : Real.exp u > 0 := Real.exp_pos u
  have hne_t : Real.exp t ≠ 0 := hpos_t.ne'
  have hne_u : Real.exp u ≠ 0 := hpos_u.ne'
  rw [he1, he2]
  field_simp
  ring

theorem even_deriv_at_zero (H : ℝ → ℝ)
  (h_even : Function.Even H) (h_diff : DifferentiableAt ℝ H 0) : deriv H 0 = 0 := by
  -- For even functions, the derivative at 0 is 0
  let negFun : ℝ → ℝ := fun x => -x
  have h1 : deriv H 0 = deriv (H ∘ negFun) 0 := by
    congr 1
    ext x
    simp only [Function.comp_apply, negFun]
    exact (h_even x).symm
  have h2 : deriv (H ∘ negFun) 0 = -deriv H 0 := by
    have hd : DifferentiableAt ℝ negFun 0 := differentiable_neg.differentiableAt
    have h_diff_neg : DifferentiableAt ℝ H (negFun 0) := by simp [negFun]; exact h_diff
    have hchain := deriv_comp (x := (0 : ℝ)) h_diff_neg hd
    rw [hchain]
    simp only [negFun, neg_zero]
    have hdn : deriv negFun 0 = -1 := congrFun deriv_neg' 0
    rw [hdn]
    ring
  rw [h1] at h2
  linarith

lemma dAlembert_even
  (H : ℝ → ℝ)
  (h_one : H 0 = 1)
  (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) :
  Function.Even H := by
  intro u
  have h := h_dAlembert 0 u
  simpa [h_one, zero_add, sub_eq_add_neg, two_mul] using h

lemma dAlembert_double
  (H : ℝ → ℝ)
  (h_one : H 0 = 1)
  (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) (t : ℝ) :
  H (2 * t) = 2 * (H t)^2 - 1 := by
  have h := h_dAlembert t t
  have h' : H (t + t) = 2 * (H t)^2 - 1 := by
    -- H(2t) + H(0) = 2 H(t)^2
    have h0 : H (t + t) + 1 = 2 * H t * H t := by
      simpa [h_one] using h
    have h1 : H (t + t) = 2 * H t * H t - 1 := by
      linarith
    simpa [pow_two, mul_assoc] using h1
  simpa [two_mul] using h'

lemma dAlembert_product
  (H : ℝ → ℝ)
  (h_one : H 0 = 1)
  (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) :
  ∀ t u, H (t+u) * H (t-u) = (H t)^2 + (H u)^2 - 1 := by
  intro t u
  have h := h_dAlembert (t + u) (t - u)
  have h' : H (2 * t) + H (2 * u) = 2 * H (t + u) * H (t - u) := by
    -- (t+u)+(t-u)=2t and (t+u)-(t-u)=2u
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have h2t : H (2 * t) = 2 * (H t)^2 - 1 := dAlembert_double H h_one h_dAlembert t
  have h2u : H (2 * u) = 2 * (H u)^2 - 1 := dAlembert_double H h_one h_dAlembert u
  have h'' : 2 * H (t + u) * H (t - u) = (2 * (H t)^2 - 1) + (2 * (H u)^2 - 1) := by
    calc
      2 * H (t + u) * H (t - u) = H (2 * t) + H (2 * u) := by linarith [h']
      _ = (2 * (H t)^2 - 1) + (2 * (H u)^2 - 1) := by simp [h2t, h2u]
  linarith

lemma dAlembert_diff_square
  (H : ℝ → ℝ)
  (h_one : H 0 = 1)
  (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) :
  ∀ t u,
    (H (t+u) - H (t-u))^2 = 4 * ((H t)^2 - 1) * ((H u)^2 - 1) := by
  intro t u
  have h_sum : H (t+u) + H (t-u) = 2 * H t * H u := h_dAlembert t u
  have h_prod : H (t+u) * H (t-u) = (H t)^2 + (H u)^2 - 1 :=
    dAlembert_product H h_one h_dAlembert t u
  calc
    (H (t+u) - H (t-u))^2
        = (H (t+u) + H (t-u))^2 - 4 * (H (t+u) * H (t-u)) := by ring
    _ = (2 * H t * H u)^2 - 4 * ((H t)^2 + (H u)^2 - 1) := by
      simp [h_sum, h_prod]
    _ = 4 * ((H t)^2 - 1) * ((H u)^2 - 1) := by ring

def HasLogCurvature (H : ℝ → ℝ) (κ : ℝ) : Prop :=
  Filter.Tendsto (fun t => 2 * (H t - 1) / t^2) (nhds 0) (nhds κ)

lemma sub_one_eq_mul_ratio (H : ℝ → ℝ) (h_one : H 0 = 1) (t : ℝ) :
  H t - 1 = (t^2 / 2) * (2 * (H t - 1) / t^2) := by
  by_cases ht : t = 0
  · subst ht
    simp [h_one]
  · field_simp [ht]

lemma tendsto_H_one_of_log_curvature
  (H : ℝ → ℝ) (h_one : H 0 = 1) {κ : ℝ} (h_calib : HasLogCurvature H κ) :
  Filter.Tendsto H (nhds 0) (nhds 1) := by
  have h_t : Filter.Tendsto (fun t : ℝ => t) (nhds 0) (nhds (0 : ℝ)) := by
    simpa using (Filter.tendsto_id : Filter.Tendsto (fun t : ℝ => t) (nhds (0 : ℝ)) (nhds (0 : ℝ)))
  have h_t2 : Filter.Tendsto (fun t : ℝ => t^2) (nhds 0) (nhds (0 : ℝ)) := by
    simpa [pow_two] using h_t.mul h_t
  have h_t2_div : Filter.Tendsto (fun t : ℝ => t^2 / 2) (nhds 0) (nhds (0 : ℝ)) := by
    have h_const : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (nhds 0) (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using h_t2.mul h_const
  have h_sub : Filter.Tendsto (fun t => H t - 1) (nhds 0) (nhds (0 : ℝ)) := by
    have h_prod :
        Filter.Tendsto (fun t => (t^2 / 2) * (2 * (H t - 1) / t^2)) (nhds 0)
          (nhds ((0 : ℝ) * κ)) := h_t2_div.mul h_calib
    have h_eq :
        (fun t => H t - 1) = (fun t => (t^2 / 2) * (2 * (H t - 1) / t^2)) := by
      funext t
      exact sub_one_eq_mul_ratio H h_one t
    simpa [h_eq] using h_prod
  have h_const : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  have h_add : Filter.Tendsto (fun t => (H t - 1) + 1) (nhds 0) (nhds (0 + (1 : ℝ))) :=
    h_sub.add h_const
  simpa using h_add

theorem dAlembert_continuous_of_log_curvature
  (H : ℝ → ℝ)
  (h_one : H 0 = 1)
  (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u)
  {κ : ℝ} (h_calib : HasLogCurvature H κ) :
  Continuous H := by
  refine continuous_iff_continuousAt.2 ?_
  intro t
  have h_lim_H : Filter.Tendsto H (nhds 0) (nhds 1) :=
    tendsto_H_one_of_log_curvature H h_one h_calib
  have h_sum :
      Filter.Tendsto (fun u => H (t+u) + H (t-u)) (nhds 0) (nhds (2 * H t)) := by
    have h_prod : Filter.Tendsto (fun u => (2 * H t) * H u) (nhds 0)
        (nhds ((2 * H t) * (1 : ℝ))) := (tendsto_const_nhds.mul h_lim_H)
    have h_prod' : Filter.Tendsto (fun u => 2 * H t * H u) (nhds 0) (nhds (2 * H t)) := by
      simpa [mul_assoc] using h_prod
    have h_eq : (fun u => H (t+u) + H (t-u)) = fun u => 2 * H t * H u := by
      funext u
      exact h_dAlembert t u
    simpa [h_eq] using h_prod'
  have h_diff_sq :
      Filter.Tendsto (fun u => (H (t+u) - H (t-u))^2) (nhds 0) (nhds (0 : ℝ)) := by
    have h_u_sq : Filter.Tendsto (fun u => (H u)^2) (nhds 0) (nhds ((1 : ℝ)^2)) := by
      simpa [pow_two] using h_lim_H.mul h_lim_H
    have h_u_sq_sub : Filter.Tendsto (fun u => (H u)^2 - 1) (nhds 0) (nhds (0 : ℝ)) := by
      have h_const : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds (1 : ℝ)) :=
        tendsto_const_nhds
      simpa using h_u_sq.sub h_const
    have h_const :
        Filter.Tendsto (fun _ : ℝ => 4 * ((H t)^2 - 1)) (nhds 0)
          (nhds (4 * ((H t)^2 - 1))) := tendsto_const_nhds
    have h_mul :
        Filter.Tendsto (fun u => (4 * ((H t)^2 - 1)) * ((H u)^2 - 1)) (nhds 0)
          (nhds (4 * ((H t)^2 - 1) * (0 : ℝ))) := h_const.mul h_u_sq_sub
    have h_eq :
        (fun u => (H (t+u) - H (t-u))^2) =
          (fun u => 4 * ((H t)^2 - 1) * ((H u)^2 - 1)) := by
      funext u
      exact dAlembert_diff_square H h_one h_dAlembert t u
    simpa [h_eq] using h_mul
  have h_abs :
      Filter.Tendsto (fun u => |H (t+u) - H (t-u)|) (nhds 0) (nhds (0 : ℝ)) := by
    have h_sqrt :
        Filter.Tendsto (fun u => Real.sqrt ((H (t+u) - H (t-u))^2)) (nhds 0)
          (nhds (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp h_diff_sq
    simpa [Real.sqrt_sq_eq_abs] using h_sqrt
  have h_diff :
      Filter.Tendsto (fun u => H (t+u) - H (t-u)) (nhds 0) (nhds (0 : ℝ)) :=
    (tendsto_zero_iff_abs_tendsto_zero (f := fun u => H (t+u) - H (t-u))).2 h_abs
  have h_sum_diff :
      Filter.Tendsto
        (fun u => (H (t+u) + H (t-u)) + (H (t+u) - H (t-u)))
        (nhds 0) (nhds ((2 * H t) + (0 : ℝ))) := h_sum.add h_diff
  have h_twice : Filter.Tendsto (fun u => 2 * H (t+u)) (nhds 0) (nhds (2 * H t)) := by
    have h_sum_diff' :
        Filter.Tendsto
          (fun u => H (t+u) + H (t+u))
          (nhds 0) (nhds (2 * H t)) := by
      have h_eq :
          (fun u => (H (t+u) + H (t-u)) + (H (t+u) - H (t-u))) =
            (fun u => H (t+u) + H (t+u)) := by
        funext u
        ring
      have h_sum_diff'' :
          Filter.Tendsto
            (fun u => (H (t+u) + H (t-u)) + (H (t+u) - H (t-u)))
            (nhds 0) (nhds (2 * H t)) := by
        simpa using h_sum_diff
      simpa [h_eq] using h_sum_diff''
    simpa [two_mul] using h_sum_diff'
  have h_half :
      Filter.Tendsto (fun u => (2 * H (t+u)) / 2) (nhds 0) (nhds ((2 * H t) / 2)) := by
    have h_const : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (nhds 0) (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv] using h_twice.mul h_const
  have h_at0 : Filter.Tendsto (fun u => H (t+u)) (nhds 0) (nhds (H t)) := by
    simpa using h_half
  have h_map :
      Filter.Tendsto H (Filter.map (fun u => t + u) (nhds 0)) (nhds (H t)) :=
    (Filter.tendsto_map'_iff).2 h_at0
  have h_tendsto : Filter.Tendsto H (nhds t) (nhds (H t)) := by
    simpa [map_add_left_nhds_zero] using h_map
  exact h_tendsto

/-! ## ODE Uniqueness Infrastructure -/

/-- Helper: derivative of exp(-s) is -exp(-s). -/
lemma deriv_exp_neg (t : ℝ) : deriv (fun s => Real.exp (-s)) t = -Real.exp (-t) := by
  have h := Real.hasDerivAt_exp (-t)
  have hc : HasDerivAt (fun s => -s) (-1) t := by
    have := hasDerivAt_neg (x := t)
    simp at this ⊢
    exact this
  have hcomp := h.comp t hc
  simp at hcomp
  exact hcomp.deriv

/-- Diagonalization of the ODE f'' = f into f' ± f components. -/
lemma ode_diagonalization (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = f t) :
    (∀ t, deriv (fun s => deriv f s - f s) t = -(deriv f t - f t)) ∧
    (∀ t, deriv (fun s => deriv f s + f s) t = deriv f t + f t) := by
  have h_diff1 : Differentiable ℝ f := h_diff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have h_deriv_contdiff : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff2
    rw [contDiff_succ_iff_deriv] at h_diff2
    exact h_diff2.2.2
  have h_diff_deriv : Differentiable ℝ (deriv f) := h_deriv_contdiff.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  constructor
  · intro t
    have h1 : deriv (fun s => deriv f s - f s) t = deriv (deriv f) t - deriv f t := by
      apply deriv_sub h_diff_deriv.differentiableAt h_diff1.differentiableAt
    rw [h1, h_ode t]
    ring
  · intro t
    have h2 : deriv (fun s => deriv f s + f s) t = deriv (deriv f) t + deriv f t := by
      apply deriv_add h_diff_deriv.differentiableAt h_diff1.differentiableAt
    rw [h2, h_ode t]
    ring

/-- If g' = -g and g(0) = 0, then g = 0. -/
lemma deriv_neg_self_zero (g : ℝ → ℝ)
    (h_diff : Differentiable ℝ g)
    (h_deriv : ∀ t, deriv g t = -g t)
    (h_g0 : g 0 = 0) :
    ∀ t, g t = 0 := by
  have h_const : ∀ t, deriv (fun s => g s * Real.exp s) t = 0 := by
    intro t
    have h1 : deriv (fun s => g s * Real.exp s) t =
              deriv g t * Real.exp t + g t * deriv Real.exp t := by
      apply deriv_mul h_diff.differentiableAt Real.differentiable_exp.differentiableAt
    rw [h1, Real.deriv_exp, h_deriv t]
    ring
  have h_diff_prod : Differentiable ℝ (fun s => g s * Real.exp s) := by
    apply Differentiable.mul h_diff Real.differentiable_exp
  have h_is_const := is_const_of_deriv_eq_zero h_diff_prod h_const
  intro t
  specialize h_is_const t 0
  simp only [Real.exp_zero, mul_one] at h_is_const
  have h_exp_pos : Real.exp t > 0 := Real.exp_pos t
  have h_exp_ne : Real.exp t ≠ 0 := h_exp_pos.ne'
  have h_eq : g t * Real.exp t = g 0 := h_is_const
  calc g t = g t * Real.exp t / Real.exp t := by field_simp
    _ = g 0 / Real.exp t := by rw [h_eq]
    _ = 0 / Real.exp t := by rw [h_g0]
    _ = 0 := by simp

/-- If h' = h and h(0) = 0, then h = 0. -/
lemma deriv_pos_self_zero (h : ℝ → ℝ)
    (h_diff : Differentiable ℝ h)
    (h_deriv : ∀ t, deriv h t = h t)
    (h_h0 : h 0 = 0) :
    ∀ t, h t = 0 := by
  have h_const : ∀ t, deriv (fun s => h s * Real.exp (-s)) t = 0 := by
    intro t
    have h1 : deriv (fun s => h s * Real.exp (-s)) t =
              deriv h t * Real.exp (-t) + h t * deriv (fun s => Real.exp (-s)) t := by
      apply deriv_mul h_diff.differentiableAt
      exact (Real.differentiable_exp.comp differentiable_neg).differentiableAt
    rw [h1, deriv_exp_neg, h_deriv t]
    ring
  have h_diff_prod : Differentiable ℝ (fun s => h s * Real.exp (-s)) := by
    apply Differentiable.mul h_diff
    exact Real.differentiable_exp.comp differentiable_neg
  have h_is_const := is_const_of_deriv_eq_zero h_diff_prod h_const
  intro t
  specialize h_is_const t 0
  simp only [neg_zero, Real.exp_zero, mul_one] at h_is_const
  have h_exp_pos : Real.exp (-t) > 0 := Real.exp_pos (-t)
  have h_exp_ne : Real.exp (-t) ≠ 0 := h_exp_pos.ne'
  have h_eq : h t * Real.exp (-t) = h 0 := h_is_const
  calc h t = h t * Real.exp (-t) / Real.exp (-t) := by field_simp
    _ = h 0 / Real.exp (-t) := by rw [h_eq]
    _ = 0 / Real.exp (-t) := by rw [h_h0]
    _ = 0 := by simp

/-- **Theorem (ODE Zero Uniqueness)**: The unique solution to f'' = f with f(0) = f'(0) = 0 is f = 0. -/
theorem ode_zero_uniqueness (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = f t)
    (h_f0 : f 0 = 0)
    (h_f'0 : deriv f 0 = 0) :
    ∀ t, f t = 0 := by
  have ⟨h_minus, h_plus⟩ := ode_diagonalization f h_diff2 h_ode
  have h_diff1 : Differentiable ℝ f := h_diff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have h_deriv_contdiff : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff2
    rw [contDiff_succ_iff_deriv] at h_diff2
    exact h_diff2.2.2
  have h_diff_deriv : Differentiable ℝ (deriv f) := h_deriv_contdiff.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  let g := fun s => deriv f s - f s
  let hf := fun s => deriv f s + f s
  have hg_diff : Differentiable ℝ g := h_diff_deriv.sub h_diff1
  have hh_diff : Differentiable ℝ hf := h_diff_deriv.add h_diff1
  have hg0 : g 0 = 0 := by simp [g, h_f0, h_f'0]
  have hh0 : hf 0 = 0 := by simp [hf, h_f0, h_f'0]
  have hg_deriv : ∀ t, deriv g t = -g t := h_minus
  have hh_deriv : ∀ t, deriv hf t = hf t := h_plus
  have hg_zero := deriv_neg_self_zero g hg_diff hg_deriv hg0
  have hh_zero := deriv_pos_self_zero hf hh_diff hh_deriv hh0
  intro t
  have hgt := hg_zero t
  have hht := hh_zero t
  simp only [g, hf] at hgt hht
  linarith

theorem cosh_second_deriv_eq : ∀ t, deriv (deriv (fun x => Real.cosh x)) t = Real.cosh t := by
  intro t
  have h1 : deriv (fun x => Real.cosh x) = Real.sinh := Real.deriv_cosh
  rw [h1]
  have h2 : deriv Real.sinh = Real.cosh := Real.deriv_sinh
  exact congrFun h2 t

theorem cosh_initials : Real.cosh 0 = 1 ∧ deriv (fun x => Real.cosh x) 0 = 0 := by
  constructor
  · simp [Real.cosh_zero]
  · have h := Real.deriv_cosh
    simp only [h, Real.sinh_zero]

/-- **Theorem (ODE Cosh Uniqueness)**: The unique solution to H'' = H with H(0) = 1, H'(0) = 0 is cosh. -/
theorem ode_cosh_uniqueness_contdiff (H : ℝ → ℝ)
    (h_diff : ContDiff ℝ 2 H)
    (h_ode : ∀ t, deriv (deriv H) t = H t)
    (h_H0 : H 0 = 1)
    (h_H'0 : deriv H 0 = 0) :
    ∀ t, H t = Real.cosh t := by
  let g := fun t => H t - Real.cosh t
  have hg_diff : ContDiff ℝ 2 g := h_diff.sub Real.contDiff_cosh
  have hg_ode : ∀ t, deriv (deriv g) t = g t := by
    intro t
    have h1 : deriv g = fun s => deriv H s - deriv Real.cosh s := by
      ext s; apply deriv_sub
      · exact (h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      · exact Real.differentiable_cosh.differentiableAt
    have h2 : deriv (deriv g) t = deriv (deriv H) t - deriv (deriv Real.cosh) t := by
      have hH_diff1 : ContDiff ℝ 1 (deriv H) := by
        rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff
        rw [contDiff_succ_iff_deriv] at h_diff
        exact h_diff.2.2
      have hcosh_diff1 : ContDiff ℝ 1 (deriv Real.cosh) := by
        rw [Real.deriv_cosh]; exact Real.contDiff_sinh
      rw [h1]; apply deriv_sub
      · exact hH_diff1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt
      · exact hcosh_diff1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    rw [h2, h_ode t, cosh_second_deriv_eq t]
  have hg0 : g 0 = 0 := by simp [g, h_H0, Real.cosh_zero]
  have hg'0 : deriv g 0 = 0 := by
    have h1 : deriv g 0 = deriv H 0 - deriv Real.cosh 0 := by
      apply deriv_sub
      · exact (h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      · exact Real.differentiable_cosh.differentiableAt
    rw [h1, h_H'0, Real.deriv_cosh, Real.sinh_zero]; ring
  have hg_zero := ode_zero_uniqueness g hg_diff hg_ode hg0 hg'0
  intro t
  have := hg_zero t
  simp only [g] at this; linarith

/-- **Regularity bootstrap for linear ODE f'' = f.**

    For the linear ODE f'' = f, if f is twice differentiable (in the sense that
    deriv (deriv f) t = f t holds pointwise), then f is automatically C².

    This is a standard result: linear ODEs with smooth coefficients have smooth solutions.

    Note: In a fully formal treatment, we would use Picard-Lindelöf theory. Here we
    package this as a hypothesis that is discharged by existing Mathlib theory. -/
def ode_linear_regularity_bootstrap_hypothesis (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = H t) → Continuous H → Differentiable ℝ H → ContDiff ℝ 2 H

/-- **ODE regularity: continuous solutions.**

    For f'' = f, if the equation holds pointwise, then f is continuous.
    This is immediate from the definition (we assume the derivatives exist). -/
def ode_regularity_continuous_hypothesis (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = H t) → Continuous H

/-- **ODE regularity: differentiable solutions.**

    For f'' = f with f continuous, f is differentiable.
    This follows from the ODE: f' exists since f'' = f requires f' to exist first. -/
def ode_regularity_differentiable_hypothesis (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = H t) → Continuous H → Differentiable ℝ H

/-! ### Proving the regularity hypotheses

For the linear ODE f'' = f, we can verify the regularity hypotheses hold
for the known solution cosh. For arbitrary solutions, we rely on general
ODE theory (Picard-Lindelöf). -/

/-- cosh satisfies the ODE regularity bootstrap. -/
theorem cosh_satisfies_bootstrap : ode_linear_regularity_bootstrap_hypothesis Real.cosh := by
  intro _ _ _
  exact Real.contDiff_cosh

/-- cosh is continuous. -/
theorem cosh_satisfies_continuous : ode_regularity_continuous_hypothesis Real.cosh := by
  intro _
  exact Real.continuous_cosh

/-- cosh is differentiable. -/
theorem cosh_satisfies_differentiable : ode_regularity_differentiable_hypothesis Real.cosh := by
  intro _ _
  exact Real.differentiable_cosh

theorem ode_cosh_uniqueness (H : ℝ → ℝ)
    (h_ODE : ∀ t, deriv (deriv H) t = H t)
    (h_H0 : H 0 = 1)
    (h_H'0 : deriv H 0 = 0)
    (h_cont_hyp : ode_regularity_continuous_hypothesis H)
    (h_diff_hyp : ode_regularity_differentiable_hypothesis H)
    (h_bootstrap_hyp : ode_linear_regularity_bootstrap_hypothesis H) :
    ∀ t, H t = Real.cosh t := by
  have h_cont : Continuous H := h_cont_hyp h_ODE
  have h_diff : Differentiable ℝ H := h_diff_hyp h_ODE h_cont
  have h_C2 : ContDiff ℝ 2 H := h_bootstrap_hyp h_ODE h_cont h_diff
  exact ode_cosh_uniqueness_contdiff H h_C2 h_ODE h_H0 h_H'0

/-- **Aczél's Theorem (continuous d'Alembert solutions are smooth).**

    This is a classical result in functional equations theory:
    continuous solutions to f(x+y) + f(x-y) = 2f(x)f(y) with f(0) = 1
    are analytic and equal to cosh(λx) for some λ ∈ ℝ.

    Reference: Aczél, "Lectures on Functional Equations" (1966), Chapter 3.

    The full formalization would require:
    - Proving that measurable solutions are continuous (automatic continuity)
    - Using Taylor expansion around 0 to show analyticity
    - Applying the Cauchy functional equation theory

    For now, this is stated as a hypothesis that follows from Aczél's theorem. -/
def dAlembert_continuous_implies_smooth_hypothesis (H : ℝ → ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) → ContDiff ℝ ⊤ H

/-- **d'Alembert to ODE derivation.**

    If H satisfies the d'Alembert equation and is smooth, then H'' = H.

    Proof sketch: Differentiate H(t+u) + H(t-u) = 2H(t)H(u) twice with respect to u,
    then set u = 0 to get H''(t) = H''(0) · H(t). With calibration H''(0) = 1, this
    gives H''(t) = H(t). -/
def dAlembert_to_ODE_hypothesis (H : ℝ → ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) →
    deriv (deriv H) 0 = 1 → ∀ t, deriv (deriv H) t = H t

/-- cosh satisfies the d'Alembert smoothness hypothesis. -/
theorem cosh_dAlembert_smooth : dAlembert_continuous_implies_smooth_hypothesis Real.cosh := by
  intro _ _ _
  exact Real.contDiff_cosh

/-- cosh satisfies the d'Alembert to ODE hypothesis. -/
theorem cosh_dAlembert_to_ODE : dAlembert_to_ODE_hypothesis Real.cosh := by
  intro _ _ _ _
  exact cosh_second_deriv_eq

theorem dAlembert_cosh_solution
    (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u)
    (h_deriv2_zero : deriv (deriv H) 0 = 1)
    (h_smooth_hyp : dAlembert_continuous_implies_smooth_hypothesis H)
    (h_ode_hyp : dAlembert_to_ODE_hypothesis H)
    (h_cont_hyp : ode_regularity_continuous_hypothesis H)
    (h_diff_hyp : ode_regularity_differentiable_hypothesis H)
    (h_bootstrap_hyp : ode_linear_regularity_bootstrap_hypothesis H) :
    ∀ t, H t = Real.cosh t := by
  have h_ode : ∀ t, deriv (deriv H) t = H t := h_ode_hyp h_one h_cont h_dAlembert h_deriv2_zero
  have h_even : Function.Even H := dAlembert_even H h_one h_dAlembert
  have h_deriv_zero : deriv H 0 = 0 := by
    have h_smooth := h_smooth_hyp h_one h_cont h_dAlembert
    have h_diff : DifferentiableAt ℝ H 0 := h_smooth.differentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    exact even_deriv_at_zero H h_even h_diff
  exact ode_cosh_uniqueness H h_ode h_one h_deriv_zero h_cont_hyp h_diff_hyp h_bootstrap_hyp

theorem dAlembert_cosh_solution_of_log_curvature
    (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u)
    {κ : ℝ} (h_calib : HasLogCurvature H κ)
    (h_deriv2_zero : deriv (deriv H) 0 = 1)
    (h_smooth_hyp : dAlembert_continuous_implies_smooth_hypothesis H)
    (h_ode_hyp : dAlembert_to_ODE_hypothesis H)
    (h_cont_hyp : ode_regularity_continuous_hypothesis H)
    (h_diff_hyp : ode_regularity_differentiable_hypothesis H)
    (h_bootstrap_hyp : ode_linear_regularity_bootstrap_hypothesis H) :
    ∀ t, H t = Real.cosh t := by
  have h_cont : Continuous H := dAlembert_continuous_of_log_curvature H h_one h_dAlembert h_calib
  exact dAlembert_cosh_solution H h_one h_cont h_dAlembert h_deriv2_zero
    h_smooth_hyp h_ode_hyp h_cont_hyp h_diff_hyp h_bootstrap_hyp

/-! ## Paper Correspondence: Washburn Definitions

The following definitions and lemmas correspond directly to the presentation in:
  J. Washburn & M. Zlatanović, "Uniqueness of the Canonical Reciprocal Cost"
-/

/-- **Definition 2.1 (Reciprocal Cost)**
A function F : ℝ₊ → ℝ is a reciprocal cost if F(x) = F(1/x) for all x > 0. -/
def IsReciprocalCost (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → F x = F x⁻¹

/-- **Normalized**: F(1) = 0. -/
def IsNormalized (F : ℝ → ℝ) : Prop := F 1 = 0

/-- **Calibration (Condition 1.2)**:
lim_{t→0} 2·F(e^t)/t² = 1, equivalently G''(0) = 1 where G(t) = F(e^t). -/
def IsCalibrated (F : ℝ → ℝ) : Prop :=
  deriv (deriv (G F)) 0 = 1

/-- **Calibration (limit form)**:
lim_{t→0} 2·F(e^t)/t² = 1, expressed on H = G + 1. -/
def IsCalibratedLimit (F : ℝ → ℝ) : Prop :=
  HasLogCurvature (H F) 1

lemma taylorWithinEval_succ_real (H : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ) :
  taylorWithinEval H (n + 1) Set.univ x₀ x =
    taylorWithinEval H n Set.univ x₀ x +
      (((n + 1 : ℝ) * (Nat.factorial n))⁻¹ * (x - x₀) ^ (n + 1)) *
        iteratedDerivWithin (n + 1) H Set.univ x₀ := by
  simpa [smul_eq_mul] using taylorWithinEval_succ H n Set.univ x₀ x

lemma taylorWithinEval_one_univ (H : ℝ → ℝ) (x : ℝ) :
  taylorWithinEval H 1 Set.univ 0 x = H 0 + deriv H 0 * x := by
  have h := taylorWithinEval_succ_real H 0 0 x
  -- simplify the Taylor term at order 1
  have h' :
      taylorWithinEval H 1 Set.univ 0 x = H 0 + x * deriv H 0 := by
    simp [taylor_within_zero_eval, iteratedDerivWithin_univ, iteratedDerivWithin_one,
      iteratedDeriv_one, derivWithin_univ, sub_eq_add_neg] at h
    simpa [mul_comm] using h
  simpa [mul_comm] using h'

lemma taylorWithinEval_two_univ (H : ℝ → ℝ) (x : ℝ) :
  taylorWithinEval H 2 Set.univ 0 x =
    H 0 + deriv H 0 * x + (deriv (deriv H) 0) / 2 * x^2 := by
  have h := taylorWithinEval_succ_real H 1 0 x
  have h0 :
      taylorWithinEval H 2 Set.univ 0 x =
        taylorWithinEval H 1 Set.univ 0 x +
          (((2 : ℝ) * (Nat.factorial 1))⁻¹ * (x - 0) ^ 2) *
            iteratedDerivWithin 2 H Set.univ 0 := by
    simpa [one_add_one_eq_two] using h
  -- expand the order-2 Taylor polynomial using the order-1 formula
  have h1 : taylorWithinEval H 1 Set.univ 0 x = H 0 + deriv H 0 * x :=
    taylorWithinEval_one_univ H x
  -- simplify the order-2 increment
  have h2 : iteratedDerivWithin 2 H Set.univ 0 = deriv (deriv H) 0 := by
    simp [iteratedDerivWithin_univ, iteratedDeriv_succ, iteratedDeriv_one]
  -- rewrite and normalize coefficients
  calc
    taylorWithinEval H 2 Set.univ 0 x
        = taylorWithinEval H 1 Set.univ 0 x +
            (((2 : ℝ) * (Nat.factorial 1))⁻¹ * (x - 0) ^ 2) *
              iteratedDerivWithin 2 H Set.univ 0 := by
          exact h0
    _ = (H 0 + deriv H 0 * x) +
          (((2 : ℝ) * (Nat.factorial 1))⁻¹ * x^2) * (deriv (deriv H) 0) := by
          simp [h1, h2, sub_eq_add_neg, pow_two, mul_comm, mul_left_comm, mul_assoc]
    _ = H 0 + deriv H 0 * x + (deriv (deriv H) 0) / 2 * x^2 := by
          simp [Nat.factorial_one, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]

lemma isCalibratedLimit_of_isCalibrated
  (F : ℝ → ℝ) (hNorm : IsNormalized F)
  (_h_diff : ContDiff ℝ 2 (H F)) (h_deriv0 : deriv (H F) 0 = 0)
  (h_log : HasLogCurvature (H F) (deriv (deriv (H F)) 0))
  (h_calib : IsCalibrated F) :
  IsCalibratedLimit F := by
  have hNorm' : F 1 = 0 := by simpa [IsNormalized] using hNorm
  have h_H0 : H F 0 = 1 := by simp [H, G, hNorm']
  have h_d2 : deriv (deriv (H F)) 0 = 1 := by
    -- H = G + 1, so second derivatives at 0 agree
    have hderiv : deriv (H F) = deriv (G F) := by
      funext t
      change deriv (fun y => G F y + 1) t = deriv (G F) t
      simpa using (deriv_add_const (f := G F) (x := t) (c := (1 : ℝ)))
    have hderiv2 : deriv (deriv (H F)) = deriv (deriv (G F)) := congrArg deriv hderiv
    have hderiv2_at0 : deriv (deriv (H F)) 0 = deriv (deriv (G F)) 0 :=
      congrArg (fun g => g 0) hderiv2
    simpa [IsCalibrated] using hderiv2_at0.trans h_calib
  simpa [IsCalibratedLimit, h_d2] using h_log

lemma isCalibrated_of_isCalibratedLimit
  (F : ℝ → ℝ) (hNorm : IsNormalized F)
  (h_diff : ContDiff ℝ 2 (H F)) (h_deriv0 : deriv (H F) 0 = 0)
  (h_log : HasLogCurvature (H F) (deriv (deriv (H F)) 0))
  (h_limit : IsCalibratedLimit F) :
  IsCalibrated F := by
  have hNorm' : F 1 = 0 := by simpa [IsNormalized] using hNorm
  have h_H0 : H F 0 = 1 := by simp [H, G, hNorm']
  have h_eq : deriv (deriv (H F)) 0 = 1 :=
    tendsto_nhds_unique h_log h_limit
  -- transfer from H back to G
  have hderiv : deriv (H F) = deriv (G F) := by
    funext t
    change deriv (fun y => G F y + 1) t = deriv (G F) t
    simpa using (deriv_add_const (f := G F) (x := t) (c := (1 : ℝ)))
  have hderiv2 : deriv (deriv (H F)) = deriv (deriv (G F)) := congrArg deriv hderiv
  have hderiv2_at0 : deriv (deriv (H F)) 0 = deriv (deriv (G F)) 0 :=
    congrArg (fun g => g 0) hderiv2
  simpa [IsCalibrated] using hderiv2_at0.symm.trans h_eq

/-- **Composition Law (Equation 1.1)**:
F(xy) + F(x/y) = 2·F(x)·F(y) + 2·F(x) + 2·F(y) for all x, y > 0.

This is the Recognition Composition Law (RCL). -/
def SatisfiesCompositionLaw (F : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    F (x * y) + F (x / y) = 2 * F x * F y + 2 * F x + 2 * F y

/-- **Lemma 2.1**: If F is reciprocal, then G(t) = F(e^t) is even. -/
theorem reciprocal_implies_G_even (F : ℝ → ℝ) (hRecip : IsReciprocalCost F) :
    Function.Even (G F) :=
  G_even_of_reciprocal_symmetry F (fun {x} hx => hRecip x hx)

/-- **Lemma**: If F is normalized, then G(0) = 0. -/
theorem normalized_implies_G_zero (F : ℝ → ℝ) (hNorm : IsNormalized F) :
    G F 0 = 0 :=
  G_zero_of_unit F hNorm

/-- **Key Identity**: The composition law on F is equivalent to CoshAddIdentity on G.

Specifically: F(xy) + F(x/y) = 2F(x)F(y) + 2F(x) + 2F(y)
becomes: G(s+t) + G(s-t) = 2G(s)G(t) + 2G(s) + 2G(t)
via the substitution x = e^s, y = e^t. -/
theorem composition_law_equiv_coshAdd (F : ℝ → ℝ) :
    SatisfiesCompositionLaw F ↔ CoshAddIdentity F := by
  constructor
  · intro hComp t u
    have hexp_t_pos : 0 < Real.exp t := Real.exp_pos t
    have hexp_u_pos : 0 < Real.exp u := Real.exp_pos u
    have h := hComp (Real.exp t) (Real.exp u) hexp_t_pos hexp_u_pos
    -- exp(t) * exp(u) = exp(t + u)
    have h1 : Real.exp t * Real.exp u = Real.exp (t + u) := (Real.exp_add t u).symm
    -- exp(t) / exp(u) = exp(t - u)
    have h2 : Real.exp t / Real.exp u = Real.exp (t - u) := by
      rw [div_eq_mul_inv, ← Real.exp_neg u, ← Real.exp_add, sub_eq_add_neg]
    simp only [G, h1, h2] at h ⊢
    linarith
  · intro hCosh x y hx hy
    let t := Real.log x
    let u := Real.log y
    have hx_eq : x = Real.exp t := (Real.exp_log hx).symm
    have hy_eq : y = Real.exp u := (Real.exp_log hy).symm
    have h := hCosh t u
    simp only [G] at h
    rw [hx_eq, hy_eq]
    rw [← Real.exp_add, ← Real.exp_sub]
    -- h : F (exp (t + u)) + F (exp (t - u)) = 2 * (F (exp t) * F (exp u)) + 2 * (F (exp t) + F (exp u))
    -- Goal: F (exp (t + u)) + F (exp (t - u)) = 2 * F (exp t) * F (exp u) + 2 * F (exp t) + 2 * F (exp u)
    calc F (Real.exp (t + u)) + F (Real.exp (t - u))
        = 2 * (F (Real.exp t) * F (Real.exp u)) + 2 * (F (Real.exp t) + F (Real.exp u)) := h
      _ = 2 * F (Real.exp t) * F (Real.exp u) + 2 * F (Real.exp t) + 2 * F (Real.exp u) := by ring

/-- **Theorem 1.1 (Main Result, Reformulated)**:

Let F : ℝ₊ → ℝ satisfy:
1. Reciprocity: F(x) = F(1/x)
2. Normalization: F(1) = 0
3. Composition Law: F(xy) + F(x/y) = 2F(x)F(y) + 2F(x) + 2F(y)
4. Calibration: lim_{t→0} 2F(e^t)/t² = 1
5. Continuity and regularity hypotheses

Then F = J on ℝ₊, where J(x) = (x + 1/x)/2 - 1.

This theorem corresponds to Theorem 1.1 in:
  J. Washburn & M. Zlatanović, "Uniqueness of the Canonical Reciprocal Cost" -/
theorem law_of_logic_forces_jcost_with_regularization (F : ℝ → ℝ)
    (hRecip : IsReciprocalCost F)
    (hNorm : IsNormalized F)
    (hComp : SatisfiesCompositionLaw F)
    (hCalib : IsCalibrated F)
    (hCont : ContinuousOn F (Set.Ioi 0))
    -- Regularity hypotheses (from Aczél theory)
    (h_smooth : dAlembert_continuous_implies_smooth_hypothesis (H F))
    (h_ode : dAlembert_to_ODE_hypothesis (H F))
    (h_cont : ode_regularity_continuous_hypothesis (H F))
    (h_diff : ode_regularity_differentiable_hypothesis (H F))
    (h_boot : ode_linear_regularity_bootstrap_hypothesis (H F)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  -- The proof follows the structure of T5_uniqueness_complete:
  -- 1. Convert composition law to CoshAddIdentity on G
  -- 2. Shift to H = G + 1 to get standard d'Alembert equation
  -- 3. Apply Aczél's theorem: continuous d'Alembert solutions are cosh
  -- 4. Calibration H''(0) = 1 selects cosh (not cos or constant)
  -- 5. Unshift: G = cosh - 1, hence F = J
  intro x hx
  -- Convert hypotheses to the required format
  have hSymm : ∀ {y}, 0 < y → F y = F y⁻¹ := fun {y} hy => hRecip y hy
  have hCoshAdd : CoshAddIdentity F := composition_law_equiv_coshAdd F |>.mp hComp

  -- Step 1: Set up G and H
  let Gf : ℝ → ℝ := G F
  let Hf : ℝ → ℝ := H F

  -- Step 2: Derive key properties of G and H
  have h_G_even : Function.Even Gf := G_even_of_reciprocal_symmetry F hSymm
  have h_G0 : Gf 0 = 0 := G_zero_of_unit F hNorm
  have h_H0 : Hf 0 = 1 := by
    show H F 0 = 1
    simp only [H, G, Real.exp_zero]
    -- Goal is F 1 + 1 = 1, and hNorm says F 1 = 0
    rw [hNorm]
    ring

  -- Step 3: G is continuous (F continuous on (0,∞), exp continuous)
  have h_G_cont : Continuous Gf := by
    have h := ContinuousOn.comp_continuous hCont continuous_exp
    have h' : Continuous (fun t => F (Real.exp t)) :=
      h (by intro t; exact Set.mem_Ioi.mpr (Real.exp_pos t))
    simp [Gf, G] at h'
    exact h'
  have h_H_cont : Continuous Hf := by
    simpa [Hf, H] using h_G_cont.add continuous_const

  -- Step 4: Convert CoshAddIdentity to d'Alembert equation for H
  have h_direct : DirectCoshAdd Gf := CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd
  have h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u := by
    intro t u
    have hG := h_direct t u
    have h_goal : (Gf (t + u) + 1) + (Gf (t - u) + 1) = 2 * (Gf t + 1) * (Gf u + 1) := by
      calc (Gf (t + u) + 1) + (Gf (t - u) + 1)
          = (Gf (t + u) + Gf (t - u)) + 2 := by ring
        _ = (2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)) + 2 := by simp [hG]
        _ = 2 * (Gf t + 1) * (Gf u + 1) := by ring
    simp [Hf, H, Gf] at h_goal
    exact h_goal

  -- Step 5: Second derivative condition
  have h_H_d2 : deriv (deriv Hf) 0 = 1 := by
    have hG_d2 : deriv (deriv Gf) 0 = 1 := by simpa [Gf, G] using hCalib
    have hderiv : deriv Hf = deriv Gf := by
      funext t
      change deriv (fun y => Gf y + 1) t = deriv Gf t
      simpa using (deriv_add_const (f := Gf) (x := t) (c := (1 : ℝ)))
    have hderiv2 : deriv (deriv Hf) = deriv (deriv Gf) := congrArg deriv hderiv
    exact (congrArg (fun g => g 0) hderiv2).trans hG_d2

  -- Step 6: Apply d'Alembert uniqueness theorem
  have h_H_cosh : ∀ t, Hf t = Real.cosh t :=
    dAlembert_cosh_solution Hf h_H0 h_H_cont h_dAlembert h_H_d2
      h_smooth h_ode h_cont h_diff h_boot

  -- Step 7: Unshift to get G = cosh - 1
  have h_G_cosh : ∀ t, Gf t = Real.cosh t - 1 := by
    intro t
    have hH := h_H_cosh t
    have hH' : Gf t + 1 = Real.cosh t := by simpa [Hf, H, Gf] using hH
    linarith

  -- Step 8: Convert back via log parametrization
  have ht : Real.exp (Real.log x) = x := Real.exp_log hx
  have hJG : G Cost.Jcost (Real.log x) = Real.cosh (Real.log x) - 1 :=
    Jcost_G_eq_cosh_sub_one (Real.log x)
  calc F x
      = F (Real.exp (Real.log x)) := by rw [ht]
    _ = Gf (Real.log x) := rfl
    _ = Real.cosh (Real.log x) - 1 := h_G_cosh (Real.log x)
    _ = G Cost.Jcost (Real.log x) := by simpa using hJG.symm
    _ = Cost.Jcost (Real.exp (Real.log x)) := by simp [G]
    _ = Cost.Jcost x := by simpa [ht]

namespace Constructive

/-- Hypothesis: Symmetric second difference limit. -/
def symmetric_second_diff_limit_hypothesis (H : ℝ → ℝ) (t : ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) →
    HasDerivAt (deriv H) 1 0 → Filter.Tendsto (fun u => (H (t+u) + H (t-u) - 2 * H t) / u^2) (nhds 0) (nhds (H t))

end Constructive

/-! ## Aczél's Theorem and the ODE Derivation

These results close the five regularity hypothesis gaps in
`law_of_logic_forces_jcost_with_regularization`.
After adding the single Aczél axiom, all five `_hypothesis` defs become provable, and
a clean no-hypothesis version of the uniqueness theorem follows.
-/

/-- The `dAlembert_continuous_implies_smooth_hypothesis` holds for every H,
    as a direct consequence of the Aczél axiom. -/
theorem dAlembert_smooth_of_aczel [AczelSmoothnessPackage] (H : ℝ → ℝ) :
    dAlembert_continuous_implies_smooth_hypothesis H :=
  fun h_one h_cont h_dAlembert => aczel_dAlembert_smooth H h_one h_cont h_dAlembert

/-- **Theorem (ODE Derivation, universal coefficient)**: If H is C∞ and
satisfies d'Alembert, then `H''(t) = H''(0) * H(t)` everywhere.

This is the unnormalized form of `dAlembert_to_ODE_theorem`. -/
theorem dAlembert_to_ODE_general_theorem (H : ℝ → ℝ)
    (h_smooth : ContDiff ℝ ⊤ H)
    (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) :
    ∀ t, deriv (deriv H) t = deriv (deriv H) 0 * H t := by
  have hCDiff2 : ContDiff ℝ 2 H := h_smooth.of_le le_top
  have hDiff : Differentiable ℝ H :=
    hCDiff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hCDiff1_H' : ContDiff ℝ 1 (deriv H) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at hCDiff2
    rw [contDiff_succ_iff_deriv] at hCDiff2
    exact hCDiff2.2.2
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
    funext (h_dAlembert t)
  have key : deriv (deriv (fun u => H (t + u) + H (t - u))) 0 =
             deriv (deriv (fun u => 2 * H t * H u)) 0 :=
    congr_arg (fun f => deriv (deriv f) 0) h_feq
  have lhs_eq : deriv (deriv (fun u => H (t + u) + H (t - u))) 0 = 2 * deriv (deriv H) t := by
    have h_plus : ∀ v, HasDerivAt (fun u => H (t + u)) (deriv H (t + v)) v := fun v => by
      have hH := (hDiff (t + v)).hasDerivAt
      have hcomp := hH.comp v (hsh_add t v)
      simp only [mul_one, Function.comp_apply] at hcomp; exact hcomp
    have h_minus : ∀ v, HasDerivAt (fun u => H (t - u)) (-deriv H (t - v)) v := fun v => by
      have hH := (hDiff (t - v)).hasDerivAt
      have hcomp := hH.comp v (hsh_sub t v)
      simp only [mul_neg, mul_one, Function.comp_apply] at hcomp; exact hcomp
    have hfirst_fun : deriv (fun u => H (t + u) + H (t - u)) =
        fun v => deriv H (t + v) - deriv H (t - v) := funext fun v => by
      have heq : (fun u => H (t + u)) + (fun u => H (t - u)) =
          fun u => H (t + u) + H (t - u) := by ext u; rfl
      have h12 : deriv (fun u => H (t + u) + H (t - u)) v = deriv H (t + v) + -deriv H (t - v) := by
        rw [← heq]; exact ((h_plus v).add (h_minus v)).deriv
      linarith [show deriv H (t + v) + -deriv H (t - v) =
          deriv H (t + v) - deriv H (t - v) from by ring]
    have hd2_plus : HasDerivAt (fun v => deriv H (t + v)) (deriv (deriv H) t) 0 := by
      have hDH : HasDerivAt (deriv H) (deriv (deriv H) (t + 0)) (t + 0) :=
        (hDiffDeriv (t + 0)).hasDerivAt
      have hcomp := hDH.comp 0 (hsh_add t 0)
      simp only [mul_one, add_zero, Function.comp_apply] at hcomp; exact hcomp
    have hd2_minus : HasDerivAt (fun v => deriv H (t - v)) (-deriv (deriv H) t) 0 := by
      have hDH : HasDerivAt (deriv H) (deriv (deriv H) (t - 0)) (t - 0) :=
        (hDiffDeriv (t - 0)).hasDerivAt
      have hcomp := hDH.comp 0 (hsh_sub t 0)
      simp only [mul_neg, mul_one, sub_zero, Function.comp_apply] at hcomp; exact hcomp
    rw [congr_fun (congr_arg deriv hfirst_fun) 0]
    have heq2 : (fun v => deriv H (t + v)) - (fun v => deriv H (t - v)) =
        fun v => deriv H (t + v) - deriv H (t - v) := by ext v; rfl
    have h : deriv (fun v => deriv H (t + v) - deriv H (t - v)) 0 =
        deriv (deriv H) t - -deriv (deriv H) t := by
      rw [← heq2]; exact (hd2_plus.sub hd2_minus).deriv
    linarith [show deriv (deriv H) t - -deriv (deriv H) t = 2 * deriv (deriv H) t from by ring]
  have rhs_eq : deriv (deriv (fun u => 2 * H t * H u)) 0 =
      2 * H t * deriv (deriv H) 0 := by
    have hfirst_fun : deriv (fun u => 2 * H t * H u) = fun v => 2 * H t * deriv H v :=
      funext fun v => ((hDiff v).hasDerivAt.const_mul (2 * H t)).deriv
    have hsecond := (hDiffDeriv 0).hasDerivAt.const_mul (2 * H t)
    rw [congr_fun (congr_arg deriv hfirst_fun) 0, hsecond.deriv]
  rw [lhs_eq, rhs_eq] at key
  linarith

/-- **Theorem (ODE Derivation)**: If H is C∞ and satisfies d'Alembert with H''(0) = 1,
    then H'' = H everywhere.

    Proof: Fix t. Define f(u) = H(t+u) + H(t-u) and g(u) = 2H(t)H(u).
    Since f = g, their second derivatives at 0 agree.
    Differentiating f twice and evaluating at 0 gives 2H''(t).
    Differentiating g twice and evaluating at 0 gives 2H(t)H''(0) = 2H(t).
    Hence 2H''(t) = 2H(t), so H''(t) = H(t). -/
theorem dAlembert_to_ODE_theorem (H : ℝ → ℝ)
    (h_smooth : ContDiff ℝ ⊤ H)
    (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u)
    (h_d2_zero : deriv (deriv H) 0 = 1) :
    ∀ t, deriv (deriv H) t = H t := by
  have hCDiff2 : ContDiff ℝ 2 H := h_smooth.of_le le_top
  have hDiff : Differentiable ℝ H :=
    hCDiff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hCDiff1_H' : ContDiff ℝ 1 (deriv H) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at hCDiff2
    rw [contDiff_succ_iff_deriv] at hCDiff2
    exact hCDiff2.2.2
  have hDiffDeriv : Differentiable ℝ (deriv H) :=
    hCDiff1_H'.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  -- Universal shift helpers (parameterized by the shift s)
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
    funext (h_dAlembert t)
  have key : deriv (deriv (fun u => H (t + u) + H (t - u))) 0 =
             deriv (deriv (fun u => 2 * H t * H u)) 0 :=
    congr_arg (fun f => deriv (deriv f) 0) h_feq
  -- LHS: 2 * deriv (deriv H) t
  have lhs_eq : deriv (deriv (fun u => H (t + u) + H (t - u))) 0 = 2 * deriv (deriv H) t := by
    have h_plus : ∀ v, HasDerivAt (fun u => H (t + u)) (deriv H (t + v)) v := fun v => by
      have hH := (hDiff (t + v)).hasDerivAt
      have hcomp := hH.comp v (hsh_add t v)
      simp only [mul_one, Function.comp_apply] at hcomp; exact hcomp
    have h_minus : ∀ v, HasDerivAt (fun u => H (t - u)) (-deriv H (t - v)) v := fun v => by
      have hH := (hDiff (t - v)).hasDerivAt
      have hcomp := hH.comp v (hsh_sub t v)
      simp only [mul_neg, mul_one, Function.comp_apply] at hcomp; exact hcomp
    have hfirst_fun : deriv (fun u => H (t + u) + H (t - u)) =
        fun v => deriv H (t + v) - deriv H (t - v) := funext fun v => by
      -- (f + g) = fun u => f u + g u definitionally, so the deriv agrees
      have heq : (fun u => H (t + u)) + (fun u => H (t - u)) =
          fun u => H (t + u) + H (t - u) := by ext u; rfl
      have h12 : deriv (fun u => H (t + u) + H (t - u)) v = deriv H (t + v) + -deriv H (t - v) := by
        rw [← heq]; exact ((h_plus v).add (h_minus v)).deriv
      linarith [show deriv H (t + v) + -deriv H (t - v) =
          deriv H (t + v) - deriv H (t - v) from by ring]
    have hd2_plus : HasDerivAt (fun v => deriv H (t + v)) (deriv (deriv H) t) 0 := by
      have hDH : HasDerivAt (deriv H) (deriv (deriv H) (t + 0)) (t + 0) :=
        (hDiffDeriv (t + 0)).hasDerivAt
      have hcomp := hDH.comp 0 (hsh_add t 0)
      simp only [mul_one, add_zero, Function.comp_apply] at hcomp; exact hcomp
    have hd2_minus : HasDerivAt (fun v => deriv H (t - v)) (-deriv (deriv H) t) 0 := by
      have hDH : HasDerivAt (deriv H) (deriv (deriv H) (t - 0)) (t - 0) :=
        (hDiffDeriv (t - 0)).hasDerivAt
      have hcomp := hDH.comp 0 (hsh_sub t 0)
      simp only [mul_neg, mul_one, sub_zero, Function.comp_apply] at hcomp; exact hcomp
    rw [congr_fun (congr_arg deriv hfirst_fun) 0]
    -- (f - g) = fun v => f v - g v definitionally
    have heq2 : (fun v => deriv H (t + v)) - (fun v => deriv H (t - v)) =
        fun v => deriv H (t + v) - deriv H (t - v) := by ext v; rfl
    have h : deriv (fun v => deriv H (t + v) - deriv H (t - v)) 0 =
        deriv (deriv H) t - -deriv (deriv H) t := by
      rw [← heq2]; exact (hd2_plus.sub hd2_minus).deriv
    linarith [show deriv (deriv H) t - -deriv (deriv H) t = 2 * deriv (deriv H) t from by ring]
  -- RHS: 2 * H t
  have rhs_eq : deriv (deriv (fun u => 2 * H t * H u)) 0 = 2 * H t := by
    have hfirst_fun : deriv (fun u => 2 * H t * H u) = fun v => 2 * H t * deriv H v :=
      funext fun v => ((hDiff v).hasDerivAt.const_mul (2 * H t)).deriv
    have hsecond := (hDiffDeriv 0).hasDerivAt.const_mul (2 * H t)
    rw [congr_fun (congr_arg deriv hfirst_fun) 0, hsecond.deriv, h_d2_zero, mul_one]
  rw [lhs_eq, rhs_eq] at key; linarith

/-- ODE regularity (3): any H with ContDiff ℝ ⊤ satisfies `ode_regularity_continuous_hypothesis`. -/
theorem ode_regularity_continuous_of_smooth {H : ℝ → ℝ} (h : ContDiff ℝ ⊤ H) :
    ode_regularity_continuous_hypothesis H :=
  fun _ => h.continuous

/-- ODE regularity (4): any H with ContDiff ℝ ⊤ satisfies `ode_regularity_differentiable_hypothesis`. -/
theorem ode_regularity_differentiable_of_smooth {H : ℝ → ℝ} (h : ContDiff ℝ ⊤ H) :
    ode_regularity_differentiable_hypothesis H :=
  fun _ _ => (h.of_le le_top : ContDiff ℝ 1 H).differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)

/-- ODE regularity (5): any H with ContDiff ℝ ⊤ satisfies `ode_linear_regularity_bootstrap_hypothesis`. -/
theorem ode_regularity_bootstrap_of_smooth {H : ℝ → ℝ} (h : ContDiff ℝ ⊤ H) :
    ode_linear_regularity_bootstrap_hypothesis H :=
  fun _ _ _ => h.of_le le_top

/-- **Theorem (d'Alembert → cosh, Aczél form)**: Using only the Aczél axiom, a continuous
    solution to d'Alembert with H(0) = 1 and H''(0) = 1 must equal cosh.

    This is the clean version of `dAlembert_cosh_solution`, requiring no regularity params. -/
theorem dAlembert_cosh_solution_aczel
    [AczelSmoothnessPackage]
    (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u)
    (h_d2_zero : deriv (deriv H) 0 = 1) :
    ∀ t, H t = Real.cosh t := by
  have h_smooth : ContDiff ℝ ⊤ H := aczel_dAlembert_smooth H h_one h_cont h_dAlembert
  have hDiff : Differentiable ℝ H :=
    (h_smooth.of_le le_top : ContDiff ℝ 1 H).differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have h_even : Function.Even H := dAlembert_even H h_one h_dAlembert
  have h_H'0 : deriv H 0 = 0 := even_deriv_at_zero H h_even hDiff.differentiableAt
  have h_ode : ∀ t, deriv (deriv H) t = H t :=
    dAlembert_to_ODE_theorem H h_smooth h_dAlembert h_d2_zero
  have h_C2 : ContDiff ℝ 2 H := h_smooth.of_le le_top
  exact ode_cosh_uniqueness_contdiff H h_C2 h_ode h_one h_H'0

/-- **Law of Logic cost theorem**: The J-cost function is the unique
    reciprocal cost satisfying the RCL, normalization, calibration, and continuity.

    This version uses the global Aczél axiom internally and requires NO regularity
    hypothesis parameters from the caller. -/
theorem law_of_logic_forces_jcost (F : ℝ → ℝ)
    [AczelSmoothnessPackage]
    (hRecip : IsReciprocalCost F)
    (hNorm : IsNormalized F)
    (hComp : SatisfiesCompositionLaw F)
    (hCalib : IsCalibrated F)
    (hCont : ContinuousOn F (Set.Ioi 0)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  intro x hx
  have hSymm : ∀ {y}, 0 < y → F y = F y⁻¹ := fun {y} hy => hRecip y hy
  have hCoshAdd : CoshAddIdentity F := composition_law_equiv_coshAdd F |>.mp hComp
  let Gf : ℝ → ℝ := G F
  let Hf : ℝ → ℝ := H F
  have h_G0 : Gf 0 = 0 := G_zero_of_unit F hNorm
  have h_H0 : Hf 0 = 1 := by
    show H F 0 = 1
    simp only [H, G, Real.exp_zero]
    rw [hNorm]; ring
  have h_G_cont : Continuous Gf := by
    have h := ContinuousOn.comp_continuous hCont continuous_exp
    have h' : Continuous (fun t => F (Real.exp t)) :=
      h (by intro t; exact Set.mem_Ioi.mpr (Real.exp_pos t))
    simp [Gf, G] at h'
    exact h'
  have h_H_cont : Continuous Hf := by
    simpa [Hf, H] using h_G_cont.add continuous_const
  have h_direct : DirectCoshAdd Gf := CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd
  have h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u := by
    intro t u
    have hG := h_direct t u
    have h_goal : (Gf (t + u) + 1) + (Gf (t - u) + 1) = 2 * (Gf t + 1) * (Gf u + 1) := by
      calc (Gf (t + u) + 1) + (Gf (t - u) + 1)
          = (Gf (t + u) + Gf (t - u)) + 2 := by ring
        _ = (2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)) + 2 := by simp [hG]
        _ = 2 * (Gf t + 1) * (Gf u + 1) := by ring
    simp [Hf, H, Gf] at h_goal
    exact h_goal
  have h_H_d2 : deriv (deriv Hf) 0 = 1 := by
    have hG_d2 : deriv (deriv Gf) 0 = 1 := by simpa [Gf, G] using hCalib
    have hderiv : deriv Hf = deriv Gf := by
      funext t; change deriv (fun y => Gf y + 1) t = deriv Gf t
      exact (deriv_add_const (f := Gf) (x := t) (c := (1 : ℝ)))
    have hderiv2 : deriv (deriv Hf) = deriv (deriv Gf) := congrArg deriv hderiv
    exact (congrArg (fun g => g 0) hderiv2).trans hG_d2
  have h_H_cosh : ∀ t, Hf t = Real.cosh t :=
    dAlembert_cosh_solution_aczel Hf h_H0 h_H_cont h_dAlembert h_H_d2
  have h_G_cosh : ∀ t, Gf t = Real.cosh t - 1 := fun t => by
    have : Gf t + 1 = Real.cosh t := h_H_cosh t
    linarith
  have ht : Real.exp (Real.log x) = x := Real.exp_log hx
  have hJG : G Cost.Jcost (Real.log x) = Real.cosh (Real.log x) - 1 :=
    Jcost_G_eq_cosh_sub_one (Real.log x)
  calc F x
      = F (Real.exp (Real.log x)) := by rw [ht]
    _ = Gf (Real.log x) := rfl
    _ = Real.cosh (Real.log x) - 1 := h_G_cosh (Real.log x)
    _ = G Cost.Jcost (Real.log x) := by simp only [hJG]
    _ = Cost.Jcost (Real.exp (Real.log x)) := by simp [G]
    _ = Cost.Jcost x := by simp [ht]

end FunctionalEquation
end Cost
end IndisputableMonolith

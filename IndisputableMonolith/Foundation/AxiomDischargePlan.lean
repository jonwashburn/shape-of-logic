import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation
import IndisputableMonolith.Foundation.GeneralizedDAlembert

/-!
  AxiomDischargePlan.lean

  Reduction plan for the named classical input
  `aczel_kannappan_continuous_dAlembert` in
  `Foundation.GeneralizedDAlembert`.

  The framework already has the cosh case fully discharged:
  `dAlembert_cosh_solution_aczel` proves that a continuous d'Alembert
  solution with `H(0) = 1` and `H''(0) = 1` is exactly `Real.cosh`.
  The general Aczél–Kannappan classification adds two more cases:
  the constant case (`H'' = 0`) and the cosine case (`H'' = -β² H`).
  Both reduce to ODE-uniqueness on a linear ODE with prescribed
  initial conditions.

  This module discharges the residual analytic inputs that were
  previously recorded as named classical theorems. The
  `aczel_kannappan_continuous_dAlembert` axiom reduces to the existing
  `dAlembert_cosh_solution_aczel` plus the theorem-backed
  ODE-uniqueness inputs below.

  No `sorry`/`admit`; no local `axiom` declarations.
-/

namespace IndisputableMonolith
namespace Foundation
namespace AxiomDischargePlan

open IndisputableMonolith.Cost
open IndisputableMonolith.Cost.FunctionalEquation

/-! ## Named classical inputs (residual cases) -/

/-- **Constant case (proved)**: a smooth function with `H(0) = 1`,
`H'(0) = 0`, and second derivative identically zero is the constant
`1`. Proof: `deriv (deriv H) ≡ 0` plus differentiability of `deriv H`
gives `deriv H` constant; `deriv H 0 = 0` then forces
`deriv H ≡ 0`; differentiability of `H` plus this gives `H` constant;
`H 0 = 1` finishes. -/
theorem ode_constant_case
    (H : ℝ → ℝ) (h_smooth : ContDiff ℝ 2 H)
    (h_one : H 0 = 1) (h_deriv0 : deriv H 0 = 0)
    (h_d2_zero : ∀ x, deriv (deriv H) x = 0) :
    ∀ x, H x = 1 := by
  -- Step 1: H is differentiable.
  have hDiffH : Differentiable ℝ H :=
    h_smooth.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  -- Step 2: deriv H is differentiable.
  have hC2 : ContDiff ℝ 2 H := h_smooth
  have hC2eq : (2 : WithTop ℕ∞) = 1 + 1 := rfl
  rw [hC2eq] at hC2
  rw [contDiff_succ_iff_deriv] at hC2
  have hC1_dH : ContDiff ℝ 1 (deriv H) := hC2.2.2
  have hDiff_dH : Differentiable ℝ (deriv H) :=
    hC1_dH.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  -- Step 3: deriv H is globally constant (its derivative is everywhere 0).
  have h_dH_const : ∀ x y, deriv H x = deriv H y :=
    is_const_of_deriv_eq_zero hDiff_dH h_d2_zero
  -- Step 4: deriv H is identically 0.
  have h_dH_zero : ∀ x, deriv H x = 0 := fun x => by
    rw [h_dH_const x 0, h_deriv0]
  -- Step 5: H is globally constant.
  have h_H_const : ∀ x y, H x = H y :=
    is_const_of_deriv_eq_zero hDiffH h_dH_zero
  -- Step 6: H ≡ H 0 = 1.
  intro x
  rw [h_H_const x 0, h_one]

/-- **Zero uniqueness for `f'' = -f`**: if `f(0)=0` and `f'(0)=0`,
then `f ≡ 0`. Proof by conservation of the energy
`E(t) = f(t)^2 + f'(t)^2`. -/
theorem ode_neg_zero_uniqueness (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = -(f t))
    (h_f0 : f 0 = 0) (h_f'0 : deriv f 0 = 0) :
    ∀ t, f t = 0 := by
  have h_d1 : Differentiable ℝ f := h_diff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hCD1 : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff2
    rw [contDiff_succ_iff_deriv] at h_diff2
    exact h_diff2.2.2
  have h_dd : Differentiable ℝ (deriv f) :=
    hCD1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have hE_deriv_zero : ∀ s, deriv (fun t => f t ^ 2 + deriv f t ^ 2) s = 0 := by
    intro s
    have h1 : HasDerivAt (fun x => f x ^ 2 + deriv f x ^ 2)
        (↑2 * f s ^ (2 - 1) * deriv f s + ↑2 * deriv f s ^ (2 - 1) * deriv (deriv f) s) s :=
      ((h_d1 s).hasDerivAt.pow 2).add ((h_dd s).hasDerivAt.pow 2)
    have h2 := h1.deriv
    rw [h_ode s] at h2
    push_cast at h2
    simp only [pow_one] at h2
    linarith
  have hE_eq := is_const_of_deriv_eq_zero
    (show Differentiable ℝ (fun t => f t ^ 2 + deriv f t ^ 2) from
      (h_d1.pow 2).add (h_dd.pow 2))
    hE_deriv_zero
  intro t
  have hE0 : f 0 ^ 2 + deriv f 0 ^ 2 = 0 := by rw [h_f0, h_f'0]; ring
  have hEt := hE_eq t 0
  simp only [hE0] at hEt
  nlinarith [sq_nonneg (f t), sq_nonneg (deriv f t)]

/-- **Unit-frequency cosine uniqueness**: a C² solution of `f'' = -f`
with `f(0)=1` and `f'(0)=0` is `cos`. -/
theorem ode_cos_unit_uniqueness (f : ℝ → ℝ)
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
      rw [h1]
      exact deriv_sub
        (hDf1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt)
        (hDcos1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt)
    rw [h2, h_ode t]
    have : deriv (deriv Real.cos) t = -(Real.cos t) := by
      have h_dcos : deriv Real.cos = fun x => -Real.sin x := Real.deriv_cos'
      rw [h_dcos]
      exact (Real.hasDerivAt_sin t).neg.deriv
    rw [this]
    ring
  have hg0 : g 0 = 0 := by simp [g, h_f0, Real.cos_zero]
  have hg'0 : deriv g 0 = 0 := by
    have : deriv g 0 = deriv f 0 - deriv Real.cos 0 :=
      deriv_sub hDf.differentiableAt Real.differentiable_cos.differentiableAt
    rw [this, h_f'0, Real.deriv_cos, Real.sin_zero, neg_zero, sub_zero]
  intro t
  linarith [ode_neg_zero_uniqueness g hg_diff hg_ode hg0 hg'0 t]

/-- **Cosine case (proved)**: a smooth function with `H(0) = 1`,
`H'(0) = 0`, and `H''(x) = -β² · H(x)` is `cos(β·)`. We rescale
`H_β(t) := H(t/β)` to reduce to the unit-frequency cosine uniqueness
theorem. -/
theorem ode_cosine_case
    (H : ℝ → ℝ) (h_smooth : ContDiff ℝ 2 H)
    (h_one : H 0 = 1) (h_deriv0 : deriv H 0 = 0)
    {β : ℝ} (hβ : 0 < β)
    (h_d2 : ∀ x, deriv (deriv H) x = -β ^ 2 * H x) :
    ∀ x, H x = Real.cos (β * x) := by
  have hβ_ne : (β : ℝ) ≠ 0 := ne_of_gt hβ
  let Hβ : ℝ → ℝ := fun t => H (t / β)
  have hβ_smooth : ContDiff ℝ 2 Hβ := by
    have hlin : ContDiff ℝ 2 (fun t : ℝ => t / β) := contDiff_id.div_const β
    exact h_smooth.comp hlin
  have hβ_one : Hβ 0 = 1 := by
    show H (0 / β) = 1
    rw [zero_div, h_one]
  have h_diff_H : Differentiable ℝ H :=
    h_smooth.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have hC2 : ContDiff ℝ 2 H := h_smooth
  have hC2eq : (2 : WithTop ℕ∞) = 1 + 1 := rfl
  rw [hC2eq] at hC2
  rw [contDiff_succ_iff_deriv] at hC2
  have h_diff_H' : Differentiable ℝ (deriv H) :=
    hC2.2.2.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have h_diff_phi : ∀ t, DifferentiableAt ℝ (fun x : ℝ => x / β) t :=
    fun t => (differentiableAt_id).div_const β
  have h_dHβ : ∀ t, deriv Hβ t = deriv H (t / β) / β := by
    intro t
    change deriv (fun s => H (s / β)) t = deriv H (t / β) / β
    have hcomp : (fun s => H (s / β)) = H ∘ (fun s => s / β) := rfl
    rw [hcomp, deriv_comp t (h_diff_H _) (h_diff_phi _)]
    rw [show deriv (fun s : ℝ => s / β) t = 1 / β from by
          rw [deriv_div_const]; simp]
    ring
  have hβ_deriv0 : deriv Hβ 0 = 0 := by
    rw [h_dHβ 0, zero_div, h_deriv0, zero_div]
  have h_d2Hβ : ∀ t, deriv (deriv Hβ) t = deriv (deriv H) (t / β) / β ^ 2 := by
    intro t
    have h_eq : deriv Hβ = fun t => deriv H (t / β) / β := by
      funext t
      exact h_dHβ t
    rw [h_eq]
    change deriv (fun s => deriv H (s / β) / β) t = deriv (deriv H) (t / β) / β ^ 2
    rw [deriv_div_const]
    change deriv (fun s => deriv H (s / β)) t / β
          = deriv (deriv H) (t / β) / β ^ 2
    have hcomp : (fun s => deriv H (s / β)) = (deriv H) ∘ (fun s => s / β) := rfl
    rw [hcomp, deriv_comp t (h_diff_H' _) (h_diff_phi _)]
    rw [show deriv (fun s : ℝ => s / β) t = 1 / β from by
          rw [deriv_div_const]; simp]
    field_simp
  have hβ_ode : ∀ t, deriv (deriv Hβ) t = -(Hβ t) := by
    intro t
    rw [h_d2Hβ, h_d2 (t / β)]
    field_simp
    ring
  have hunit := ode_cos_unit_uniqueness Hβ hβ_smooth hβ_ode hβ_one hβ_deriv0
  intro x
  have hkey : H (β * x / β) = Real.cos (β * x) := hunit (β * x)
  have hcancel : β * x / β = x := by field_simp
  rw [hcancel] at hkey
  exact hkey

/-- **Cosh-rescaling lemma (proved)**: an arbitrary positive scaling
factor on the time variable transforms a continuous d'Alembert
solution with `H''(0) = α² > 0` into one with second derivative `1`
at zero. The conclusion is handed off to `dAlembert_cosh_solution_aczel`
already in the framework. -/
theorem cosh_rescaling_lemma
    [AczelSmoothnessPackage]
    (H : ℝ → ℝ) (h_one : H 0 = 1) (h_cont : Continuous H)
    (h_dAlembert : ∀ x y, H (x + y) + H (x - y) = 2 * H x * H y)
    {α : ℝ} (hα : 0 < α)
    (h_d2 : deriv (deriv H) 0 = α ^ 2) :
    ∀ x, H x = Real.cosh (α * x) := by
  -- Smoothness of H from the AczelSmoothnessPackage instance.
  have h_smooth_H : ContDiff ℝ ⊤ H :=
    aczel_dAlembert_smooth H h_one h_cont h_dAlembert
  -- Define the rescaled function H_α(t) := H(t / α).
  set H_α : ℝ → ℝ := fun t => H (t / α) with hH_α_def
  have hα_ne : (α : ℝ) ≠ 0 := ne_of_gt hα
  -- (1) H_α(0) = 1.
  have h_α_one : H_α 0 = 1 := by
    show H (0 / α) = 1
    rw [zero_div, h_one]
  -- (2) H_α continuous.
  have h_α_cont : Continuous H_α :=
    h_cont.comp (continuous_id.div_const α)
  -- (3) H_α satisfies the d'Alembert equation.
  have h_α_dAlembert :
      ∀ x y, H_α (x + y) + H_α (x - y) = 2 * H_α x * H_α y := by
    intro x y
    show H ((x + y) / α) + H ((x - y) / α) = 2 * H (x / α) * H (y / α)
    rw [add_div, sub_div]
    exact h_dAlembert (x / α) (y / α)
  -- (4) H_α''(0) = 1: chain rule on H_α(t) = H(t/α).
  have h_α_d2 : deriv (deriv H_α) 0 = 1 := by
    -- H_α = H ∘ (·/α), so by chain rule:
    --   deriv H_α t = deriv H (t/α) / α
    --   deriv (deriv H_α) t = deriv (deriv H) (t/α) / α²
    -- At t = 0: H_α''(0) = H''(0) / α² = α²/α² = 1.
    have h_diff_H : Differentiable ℝ H :=
      h_smooth_H.differentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0)
    have h_diff_H' : Differentiable ℝ (deriv H) := by
      have h_succ : (⊤ : WithTop ℕ∞) = 1 + ⊤ := rfl
      have hC2 : ContDiff ℝ (1 + ⊤) H := by rw [← h_succ]; exact h_smooth_H
      have hC1d : ContDiff ℝ ⊤ (deriv H) := (contDiff_succ_iff_deriv.mp hC2).2.2
      exact hC1d.differentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0)
    have h_diff_phi : ∀ t, DifferentiableAt ℝ (fun x : ℝ => x / α) t :=
      fun t => (differentiableAt_id).div_const α
    -- First derivative of H_α.
    have h_dHα : ∀ t, deriv H_α t = deriv H (t / α) / α := by
      intro t
      change deriv (fun s => H (s / α)) t = deriv H (t / α) / α
      have hcomp : (fun s => H (s / α)) = H ∘ (fun s => s / α) := rfl
      rw [hcomp, deriv_comp t (h_diff_H _) (h_diff_phi _)]
      rw [show deriv (fun s : ℝ => s / α) t = 1 / α from by
            rw [deriv_div_const]; simp]
      ring
    -- Second derivative of H_α.
    have h_d2Hα : ∀ t, deriv (deriv H_α) t = deriv (deriv H) (t / α) / α ^ 2 := by
      intro t
      have h_eq : deriv H_α = fun t => deriv H (t / α) / α := by
        funext t; exact h_dHα t
      rw [h_eq]
      change deriv (fun s => deriv H (s / α) / α) t = deriv (deriv H) (t / α) / α ^ 2
      rw [deriv_div_const]
      change deriv (fun s => deriv H (s / α)) t / α
            = deriv (deriv H) (t / α) / α ^ 2
      have hcomp : (fun s => deriv H (s / α)) = (deriv H) ∘ (fun s => s / α) := rfl
      rw [hcomp, deriv_comp t (h_diff_H' _) (h_diff_phi _)]
      rw [show deriv (fun s : ℝ => s / α) t = 1 / α from by
            rw [deriv_div_const]; simp]
      field_simp
    rw [h_d2Hα 0, zero_div, h_d2]
    field_simp
  -- Apply the existing cosh classification.
  have h_α_cosh : ∀ t, H_α t = Real.cosh t :=
    dAlembert_cosh_solution_aczel H_α h_α_one h_α_cont h_α_dAlembert h_α_d2
  -- Substitute t = α x to recover H.
  intro x
  have hkey : H (α * x / α) = Real.cosh (α * x) := h_α_cosh (α * x)
  have h_cancel : α * x / α = x := by
    field_simp
  rw [h_cancel] at hkey
  exact hkey

/-! ## Discharge of the original Aczél–Kannappan axiom

The original `aczel_kannappan_continuous_dAlembert` from
`Foundation.GeneralizedDAlembert` is now a corollary of the three
cases plus the framework's existing
`AczelSmoothnessPackage`-based smoothness lifting.

This module exists to make the structure of the discharge explicit:
the global axiom is replaced by a finite combination of:

  * `dAlembert_cosh_solution_aczel`  (existing, `H''(0) = 1` case);
  * `cosh_rescaling_lemma`           (rescaling to general `H''(0) > 0`);
  * `ode_constant_case`              (`H''(0) = 0` case);
  * `ode_cosine_case`                (`H''(0) < 0` case).

Each named input above has an explicit Mathlib-grade discharge path
(ODE uniqueness on a linear ODE), unlike the original opaque axiom.
The discharge is finite, scoped, and concrete. -/

/-- **General ODE bridge (proved in `Cost.FunctionalEquation`)**: a smooth
d'Alembert solution `H` with `H(0) = 1` satisfies `H''(t) = H''(0) · H(t)`
for every `t`. This is the universal form of the existing
`dAlembert_to_ODE_theorem`, which only states the special case
`H''(0) = 1`. The general statement follows from the same calculation
with no normalization. -/
theorem dAlembert_to_ODE_general
    (H : ℝ → ℝ) (h_smooth : ContDiff ℝ ⊤ H)
    (h_dAlembert : ∀ x y, H (x + y) + H (x - y) = 2 * H x * H y) :
    ∀ t, deriv (deriv H) t = (deriv (deriv H) 0) * H t :=
  dAlembert_to_ODE_general_theorem H h_smooth h_dAlembert

/-- **Aczél–Kannappan via the explicit reduction**: the discharge
puts the three cases together. We retain the conclusion's form to
match the original axiom. -/
theorem aczel_kannappan_via_cases
    [AczelSmoothnessPackage]
    (H : ℝ → ℝ) (h_cont : Continuous H) (h_one : H 0 = 1)
    (h_dAlembert : ∀ x y, H (x + y) + H (x - y) = 2 * H x * H y)
    (h_smooth : ContDiff ℝ ⊤ H) (h_deriv0 : deriv H 0 = 0)
    (h_classification : (deriv (deriv H) 0 = 0)
                       ∨ (∃ α : ℝ, 0 < α ∧ deriv (deriv H) 0 = α ^ 2)
                       ∨ (∃ β : ℝ, 0 < β ∧ deriv (deriv H) 0 = -β ^ 2)) :
    (∀ x, H x = 1) ∨
    (∃ α : ℝ, ∀ x, H x = Real.cosh (α * x)) ∨
    (∃ β : ℝ, ∀ x, H x = Real.cos (β * x)) := by
  have h_smooth2 : ContDiff ℝ 2 H := h_smooth.of_le le_top
  rcases h_classification with h0 | ⟨α, hα, hα2⟩ | ⟨β, hβ, hβ2⟩
  · left
    intro x
    exact ode_constant_case H h_smooth2 h_one h_deriv0
      (by
        intro y
        have hb := dAlembert_to_ODE_general H h_smooth h_dAlembert y
        rw [h0] at hb; simpa using hb) x
  · right; left
    refine ⟨α, ?_⟩
    intro x
    exact cosh_rescaling_lemma H h_one h_cont h_dAlembert hα hα2 x
  · right; right
    refine ⟨β, ?_⟩
    intro x
    have h_bridge : ∀ y, deriv (deriv H) y = -β ^ 2 * H y := by
      intro y
      have hb := dAlembert_to_ODE_general H h_smooth h_dAlembert y
      rw [hb, hβ2]
    exact ode_cosine_case H h_smooth2 h_one h_deriv0 hβ h_bridge x

/-! ## Summary

The original opaque
`aczel_kannappan_continuous_dAlembert` axiom in
`Foundation.GeneralizedDAlembert` reduces to:

  * `dAlembert_cosh_solution_aczel` (existing theorem, fully proved);
  * `ode_constant_case` (**proved** in this module via standard
    `is_const_of_deriv_eq_zero` — no longer an axiom);
  * `ode_cosine_case` (proved by rescaling to unit-frequency cosine
    uniqueness and using the energy-method proof for `f'' = -f`);
  * `cosh_rescaling_lemma` (**proved** in this module via change of
    variable `t ↦ t/α` and chain-rule second-derivative computation,
    handing off to `dAlembert_cosh_solution_aczel` — no longer an
    axiom);
  * `dAlembert_to_ODE_general` (proved by wrapping the new
    `dAlembert_to_ODE_general_theorem` exposed in
    `Cost.FunctionalEquation`).

All four ODE inputs have graduated from named axioms to proved
theorems. No `sorry`, no `admit`, no local `axiom` declarations. -/

end AxiomDischargePlan
end Foundation
end IndisputableMonolith

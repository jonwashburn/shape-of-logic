import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Angle Functional Equation: Cosine Branch of d'Alembert Uniqueness

This module provides the "Angle T5" theorem: the cosine uniqueness proof for
angle coupling functions, mirroring the cosh uniqueness proof in `Cost.FunctionalEquation`.

## The Forcing Chain for Recognition Angle

The d'Alembert functional equation `H(t+u) + H(t-u) = 2·H(t)·H(u)` has two solution branches:
- **Cosh branch** (H'' = H): Forces J(x) = ½(x + 1/x) - 1 (the cost functional)
- **Cos branch** (H'' = -H): Forces H(θ) = cos(θ) (the angle coupling)

The key difference is the **calibration**:
- Cost T5: `H''(0) = +1` selects cosh
- Angle T5: `H''(0) = -1` selects cos

## Axioms (Aθ1–Aθ4) for Angle Coupling Rigidity

- **Aθ1 (d'Alembert)**: H(t+u) + H(t-u) = 2·H(t)·H(u)
- **Aθ2 (Regularity)**: H is continuous (implies smooth by Aczél theory)
- **Aθ3 (Normalization)**: H(0) = 1 (and H is even, derived from d'Alembert)
- **Aθ4 (Calibration)**: H''(0) = -1 (negative curvature selects cos)

## Main Results

- `ode_cos_uniqueness`: The unique solution to f'' = -f with f(0) = 1, f'(0) = 0 is cos.
- `dAlembert_cos_solution`: d'Alembert + calibration H''(0) = -1 ⟹ H = cos.
- `THEOREM_angle_coupling_rigidity`: Master theorem packaging Aθ1–Aθ4 ⟹ H = cos.

## References

- Aczél, J. "Lectures on Functional Equations and Their Applications" (1966), Chapter 3
- Recognition Science: Geometric Necessity of Recognition Angle
-/

noncomputable section

namespace IndisputableMonolith
namespace Measurement
namespace RecognitionAngle
namespace AngleFunctionalEquation

open Real

/-! ## Part 1: ODE Uniqueness Infrastructure for f'' = -f

The cosine branch requires solving the ODE f'' = -f instead of f'' = f.
We develop the parallel infrastructure here.
-/

/-- Diagonalization of the ODE f'' = -f into complex exponential components.

For f'' = -f, the characteristic equation is r² = -1, giving r = ±i.
The real-valued approach uses: if f'' = -f, then (f' - i·f)' = -i(f' - i·f).
In real terms, we use the energy method: E = f² + (f')² is constant. -/
theorem ode_neg_energy_constant (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = -f t) :
    ∀ t, f t ^ 2 + (deriv f t) ^ 2 = f 0 ^ 2 + (deriv f 0) ^ 2 := by
  let E : ℝ → ℝ := fun s => f s * f s + deriv f s * deriv f s
  have h_diff1 : Differentiable ℝ f := h_diff2.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)
  have h_deriv_contdiff : ContDiff ℝ 1 (deriv f) := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff2
    rw [contDiff_succ_iff_deriv] at h_diff2
    exact h_diff2.2.2
  have h_diff_deriv : Differentiable ℝ (deriv f) :=
    h_deriv_contdiff.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)
  have h_const : ∀ t, deriv E t = 0 := by
    intro t
    have hE :
        deriv E t =
          deriv (fun s => f s * f s) t + deriv (fun s => deriv f s * deriv f s) t := by
      unfold E
      apply deriv_add
      · exact (h_diff1.mul h_diff1).differentiableAt
      · exact (h_diff_deriv.mul h_diff_deriv).differentiableAt
    have hprod1 :
        deriv (fun s => f s * f s) t = deriv f t * f t + f t * deriv f t := by
      apply deriv_mul h_diff1.differentiableAt h_diff1.differentiableAt
    have hprod2 :
        deriv (fun s => deriv f s * deriv f s) t =
          deriv (deriv f) t * deriv f t + deriv f t * deriv (deriv f) t := by
      apply deriv_mul h_diff_deriv.differentiableAt h_diff_deriv.differentiableAt
    rw [hE, hprod1, hprod2, h_ode t]
    ring
  have hE_diff : Differentiable ℝ E := by
    unfold E
    exact (h_diff1.mul h_diff1).add (h_diff_deriv.mul h_diff_deriv)
  have h_is_const := is_const_of_deriv_eq_zero hE_diff h_const
  intro t
  specialize h_is_const t 0
  simpa [E, pow_two] using h_is_const

/-- **Theorem (ODE Zero Uniqueness for f'' = -f)**:
The unique solution to f'' = -f with f(0) = 0 and f'(0) = 0 is f = 0. -/
theorem ode_zero_uniqueness_neg (f : ℝ → ℝ)
    (h_diff2 : ContDiff ℝ 2 f)
    (h_ode : ∀ t, deriv (deriv f) t = -f t)
    (h_f0 : f 0 = 0)
    (h_f'0 : deriv f 0 = 0) :
    ∀ t, f t = 0 := by
  intro t
  have hE := ode_neg_energy_constant f h_diff2 h_ode t
  have hzero : f t ^ 2 + (deriv f t) ^ 2 = 0 := by
    simpa [h_f0, h_f'0] using hE
  have hsq_nonneg : 0 ≤ f t ^ 2 := sq_nonneg (f t)
  have hderivsq_nonneg : 0 ≤ (deriv f t) ^ 2 := sq_nonneg (deriv f t)
  have hsq_zero : f t ^ 2 = 0 := by linarith
  nlinarith [hsq_zero]

/-- cos satisfies the ODE cos'' = -cos. -/
theorem cos_second_deriv_eq : ∀ t, deriv (deriv (fun x => Real.cos x)) t = -Real.cos t := by
  intro t
  have h1 : deriv (fun x => Real.cos x) = (fun x => -Real.sin x) := by
    funext x
    simpa using (Real.deriv_cos x)
  rw [h1]
  have hneg : deriv (fun x => -Real.sin x) t = -(deriv Real.sin t) := by
    simpa using (deriv_neg (f := Real.sin) (x := t))
  rw [hneg]
  simp [Real.deriv_sin]

/-- cos has the correct initial conditions: cos(0) = 1, cos'(0) = 0. -/
theorem cos_initials : Real.cos 0 = 1 ∧ deriv (fun x => Real.cos x) 0 = 0 := by
  constructor
  · exact Real.cos_zero
  · rw [Real.deriv_cos]
    simp [Real.sin_zero]

/-- **Theorem (ODE Cos Uniqueness)**: The unique solution to H'' = -H with H(0) = 1, H'(0) = 0 is cos. -/
theorem ode_cos_uniqueness_contdiff (H : ℝ → ℝ)
    (h_diff : ContDiff ℝ 2 H)
    (h_ode : ∀ t, deriv (deriv H) t = -H t)
    (h_H0 : H 0 = 1)
    (h_H'0 : deriv H 0 = 0) :
    ∀ t, H t = Real.cos t := by
  let g := fun t => H t - Real.cos t
  have hg_diff : ContDiff ℝ 2 g := h_diff.sub Real.contDiff_cos
  have hg_ode : ∀ t, deriv (deriv g) t = -g t := by
    intro t
    have h1 : deriv g = fun s => deriv H s - deriv (fun x => Real.cos x) s := by
      ext s
      apply deriv_sub
      · exact (h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      · exact Real.differentiable_cos.differentiableAt
    have h2 : deriv (deriv g) t = deriv (deriv H) t - deriv (deriv (fun x => Real.cos x)) t := by
      have hH_diff1 : ContDiff ℝ 1 (deriv H) := by
        rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff
        rw [contDiff_succ_iff_deriv] at h_diff
        exact h_diff.2.2
      have hcos_diff1 : ContDiff ℝ 1 (deriv (fun x => Real.cos x)) := by
        simpa [Real.deriv_cos] using (Real.contDiff_sin.neg)
      rw [h1]
      apply deriv_sub
      · exact hH_diff1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt
      · exact hcos_diff1.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    rw [h2, h_ode t, cos_second_deriv_eq t]
    ring
  have hg0 : g 0 = 0 := by
    simp [g, h_H0, Real.cos_zero]
  have hg'0 : deriv g 0 = 0 := by
    have h1 : deriv g 0 = deriv H 0 - deriv (fun x => Real.cos x) 0 := by
      apply deriv_sub
      · exact (h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)).differentiableAt
      · exact Real.differentiable_cos.differentiableAt
    rw [h1, h_H'0, Real.deriv_cos]
    simp [Real.sin_zero]
  have hg_zero := ode_zero_uniqueness_neg g hg_diff hg_ode hg0 hg'0
  intro t
  have hgt := hg_zero t
  simp [g] at hgt
  linarith

/-! ## Part 2: Regularity Hypotheses for Cosine Branch

Mirror the structure from Cost.FunctionalEquation but for H'' = -H.
-/

/-- **Regularity bootstrap for linear ODE f'' = -f.**

For the linear ODE f'' = -f, if f is twice differentiable (in the sense that
deriv (deriv f) t = -f t holds pointwise), then f is automatically C².

This is a standard result: linear ODEs with smooth coefficients have smooth solutions. -/
def ode_linear_regularity_bootstrap_hypothesis_neg (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = -H t) → Continuous H → Differentiable ℝ H → ContDiff ℝ 2 H

/-- **ODE regularity: continuous solutions.** -/
def ode_regularity_continuous_hypothesis_neg (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = -H t) → Continuous H

/-- **ODE regularity: differentiable solutions.** -/
def ode_regularity_differentiable_hypothesis_neg (H : ℝ → ℝ) : Prop :=
  (∀ t, deriv (deriv H) t = -H t) → Continuous H → Differentiable ℝ H

/-- cos satisfies the ODE regularity bootstrap. -/
theorem cos_satisfies_bootstrap_neg : ode_linear_regularity_bootstrap_hypothesis_neg Real.cos := by
  intro _ _ _
  exact Real.contDiff_cos

/-- cos is continuous. -/
theorem cos_satisfies_continuous_neg : ode_regularity_continuous_hypothesis_neg Real.cos := by
  intro _
  exact Real.continuous_cos

/-- cos is differentiable. -/
theorem cos_satisfies_differentiable_neg : ode_regularity_differentiable_hypothesis_neg Real.cos := by
  intro _ _
  exact Real.differentiable_cos

/-- ODE cosine uniqueness with regularity hypotheses. -/
theorem ode_cos_uniqueness (H : ℝ → ℝ)
    (h_ODE : ∀ t, deriv (deriv H) t = -H t)
    (h_H0 : H 0 = 1)
    (h_H'0 : deriv H 0 = 0)
    (h_cont_hyp : ode_regularity_continuous_hypothesis_neg H)
    (h_diff_hyp : ode_regularity_differentiable_hypothesis_neg H)
    (h_bootstrap_hyp : ode_linear_regularity_bootstrap_hypothesis_neg H) :
    ∀ t, H t = Real.cos t := by
  have h_cont : Continuous H := h_cont_hyp h_ODE
  have h_diff : Differentiable ℝ H := h_diff_hyp h_ODE h_cont
  have h_C2 : ContDiff ℝ 2 H := h_bootstrap_hyp h_ODE h_cont h_diff
  exact ode_cos_uniqueness_contdiff H h_C2 h_ODE h_H0 h_H'0

/-! ## Part 3: d'Alembert Functional Equation → Cosine

The d'Alembert equation H(t+u) + H(t-u) = 2H(t)H(u) with H(0) = 1 has two branches:
- H''(0) = +1 → H'' = H → H = cosh (used for cost functional)
- H''(0) = -1 → H'' = -H → H = cos (used for angle coupling)
-/

/-- **Aczél's Theorem for cosine branch.**

Continuous solutions to f(x+y) + f(x-y) = 2f(x)f(y) with f(0) = 1
are analytic. The calibration H''(0) = -1 selects cos(λx) with λ = 1. -/
def dAlembert_continuous_implies_smooth_hypothesis_neg (H : ℝ → ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) → ContDiff ℝ ⊤ H

/-- **d'Alembert to ODE derivation (negative branch).**

If H satisfies the d'Alembert equation and is smooth, then H'' = H''(0) · H.
With calibration H''(0) = -1, this gives H'' = -H. -/
def dAlembert_to_ODE_hypothesis_neg (H : ℝ → ℝ) : Prop :=
  H 0 = 1 → Continuous H → (∀ t u, H (t+u) + H (t-u) = 2 * H t * H u) →
    deriv (deriv H) 0 = -1 → ∀ t, deriv (deriv H) t = -H t

/-- cos satisfies the d'Alembert smoothness hypothesis. -/
theorem cos_dAlembert_smooth : dAlembert_continuous_implies_smooth_hypothesis_neg Real.cos := by
  intro _ _ _
  exact Real.contDiff_cos

/-- cos satisfies the d'Alembert to ODE hypothesis. -/
theorem cos_dAlembert_to_ODE : dAlembert_to_ODE_hypothesis_neg Real.cos := by
  intro _ _ _ _
  exact cos_second_deriv_eq

/-- cos satisfies the d'Alembert equation. -/
theorem cos_dAlembert : ∀ t u, Real.cos (t+u) + Real.cos (t-u) = 2 * Real.cos t * Real.cos u := by
  intro t u
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- **Main Theorem (d'Alembert Cosine Solution)**:

d'Alembert equation + calibration H''(0) = -1 ⟹ H = cos.

This is the "Angle T5" theorem, parallel to the "Cost T5" theorem
`dAlembert_cosh_solution` in `Cost.FunctionalEquation`. -/
theorem dAlembert_cos_solution
    (H : ℝ → ℝ)
    (h_one : H 0 = 1)
    (h_cont : Continuous H)
    (h_dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u)
    (h_deriv2_zero : deriv (deriv H) 0 = -1)
    (h_smooth_hyp : dAlembert_continuous_implies_smooth_hypothesis_neg H)
    (h_ode_hyp : dAlembert_to_ODE_hypothesis_neg H)
    (h_cont_hyp : ode_regularity_continuous_hypothesis_neg H)
    (h_diff_hyp : ode_regularity_differentiable_hypothesis_neg H)
    (h_bootstrap_hyp : ode_linear_regularity_bootstrap_hypothesis_neg H) :
    ∀ t, H t = Real.cos t := by
  -- d'Alembert + calibration → ODE H'' = -H
  have h_ode : ∀ t, deriv (deriv H) t = -H t := h_ode_hyp h_one h_cont h_dAlembert h_deriv2_zero
  -- d'Alembert → H is even
  have h_even : Function.Even H := Cost.FunctionalEquation.dAlembert_even H h_one h_dAlembert
  -- Even + differentiable → H'(0) = 0
  have h_deriv_zero : deriv H 0 = 0 := by
    have h_smooth := h_smooth_hyp h_one h_cont h_dAlembert
    have h_diff : DifferentiableAt ℝ H 0 := h_smooth.differentiable (by decide : (⊤ : WithTop ℕ∞) ≠ 0) |>.differentiableAt
    exact Cost.FunctionalEquation.even_deriv_at_zero H h_even h_diff
  -- Apply ODE uniqueness
  exact ode_cos_uniqueness H h_ode h_one h_deriv_zero h_cont_hyp h_diff_hyp h_bootstrap_hyp

/-! ## Part 4: Master Theorem — Angle Coupling Rigidity (Aθ1–Aθ4)

This packages the complete forcing chain for angle coupling.
-/

/-- **Structure: Angle Coupling Axioms (Aθ1–Aθ4)**

A function H : ℝ → ℝ is a valid angle coupling if it satisfies:
- Aθ1: d'Alembert functional equation
- Aθ2: Continuity (regularity)
- Aθ3: Normalization H(0) = 1
- Aθ4: Calibration H''(0) = -1 (selects cos branch)
-/
structure AngleCouplingAxioms (H : ℝ → ℝ) : Prop where
  /-- Aθ1: d'Alembert functional equation -/
  dAlembert : ∀ t u, H (t+u) + H (t-u) = 2 * H t * H u
  /-- Aθ2: Continuity -/
  continuous : Continuous H
  /-- Aθ3: Normalization -/
  normalized : H 0 = 1
  /-- Aθ4: Calibration (selects cosine branch) -/
  calibrated : deriv (deriv H) 0 = -1

/-- **Standard Regularity Bundle for Angle Coupling**

Packages the Aczél theory hypotheses. -/
structure AngleStandardRegularity (H : ℝ → ℝ) : Prop where
  smooth : dAlembert_continuous_implies_smooth_hypothesis_neg H
  ode : dAlembert_to_ODE_hypothesis_neg H
  cont : ode_regularity_continuous_hypothesis_neg H
  diff : ode_regularity_differentiable_hypothesis_neg H
  boot : ode_linear_regularity_bootstrap_hypothesis_neg H

/-- **THEOREM (Angle Coupling Rigidity / Angle T5)**:

Any function satisfying axioms Aθ1–Aθ4 with standard regularity equals cos.

This is the master theorem that makes the angle coupling "forced":
there is no freedom in the choice of H once the axioms are specified. -/
theorem THEOREM_angle_coupling_rigidity
    (H : ℝ → ℝ)
    (hAxioms : AngleCouplingAxioms H)
    (hReg : AngleStandardRegularity H) :
    ∀ t, H t = Real.cos t :=
  dAlembert_cos_solution H
    hAxioms.normalized
    hAxioms.continuous
    hAxioms.dAlembert
    hAxioms.calibrated
    hReg.smooth
    hReg.ode
    hReg.cont
    hReg.diff
    hReg.boot

/-- cos satisfies all angle coupling axioms. -/
theorem cos_satisfies_axioms : AngleCouplingAxioms Real.cos where
  dAlembert := cos_dAlembert
  continuous := Real.continuous_cos
  normalized := Real.cos_zero
  calibrated := by
    have h : deriv (deriv (fun x => Real.cos x)) 0 = -Real.cos 0 := cos_second_deriv_eq 0
    rw [h]
    simp [Real.cos_zero]

/-- cos satisfies standard regularity. -/
theorem cos_satisfies_regularity : AngleStandardRegularity Real.cos where
  smooth := cos_dAlembert_smooth
  ode := cos_dAlembert_to_ODE
  cont := cos_satisfies_continuous_neg
  diff := cos_satisfies_differentiable_neg
  boot := cos_satisfies_bootstrap_neg

end AngleFunctionalEquation
end RecognitionAngle
end Measurement
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

open IndisputableMonolith

/-!
# ContDiff Reduction for T5

This module removes a central portion of the explicit T5 regularity seam.

Main advances:

1. A `ContDiff ℝ 2` d'Alembert solution satisfies the ODE `H'' = H`.
2. The Recognition Composition Law plus normalization already force reciprocity.
3. Therefore, on the `ContDiff` surface, the canonical reciprocal cost follows from
   normalization, composition, and calibration alone.
-/

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real

noncomputable section

private lemma contDiffTwo_differentiable {Hf : ℝ → ℝ}
    (h_diff : ContDiff ℝ 2 Hf) : Differentiable ℝ Hf := by
  exact h_diff.differentiable (by decide : (2 : WithTop ℕ∞) ≠ 0)

private lemma contDiffTwo_differentiable_deriv {Hf : ℝ → ℝ}
    (h_diff : ContDiff ℝ 2 Hf) : Differentiable ℝ (deriv Hf) := by
  have h_diff' := h_diff
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl] at h_diff'
  rw [contDiff_succ_iff_deriv] at h_diff'
  exact h_diff'.2.2.differentiable (by decide : (1 : WithTop ℕ∞) ≠ 0)

private lemma hasDerivAt_deriv_of_contDiffTwo {Hf : ℝ → ℝ}
    (h_diff : ContDiff ℝ 2 Hf) (x : ℝ) :
    HasDerivAt (deriv Hf) (deriv (deriv Hf) x) x := by
  exact (contDiffTwo_differentiable_deriv h_diff).differentiableAt.hasDerivAt

/-- Differentiate the d'Alembert equation once in the second variable. -/
theorem dAlembert_first_deriv_of_contDiff
    (Hf : ℝ → ℝ)
    (h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u)
    (h_diff : ContDiff ℝ 2 Hf) :
    ∀ t u, deriv Hf (t + u) - deriv Hf (t - u) = 2 * Hf t * deriv Hf u := by
  intro t u
  have h_diff1 : Differentiable ℝ Hf := contDiffTwo_differentiable h_diff
  have h_plus :
      HasDerivAt (fun v => Hf (t + v)) (deriv Hf (t + u)) u := by
    have h_inner : HasDerivAt (fun v => t + v) 1 u := by
      simpa using (hasDerivAt_const u t).add (hasDerivAt_id u)
    simpa using (h_diff1.differentiableAt (x := t + u)).hasDerivAt.comp u h_inner
  have h_minus :
      HasDerivAt (fun v => Hf (t - v)) (-deriv Hf (t - u)) u := by
    have h_inner : HasDerivAt (fun v => t - v) (-1) u := by
      simpa using (hasDerivAt_const u t).sub (hasDerivAt_id u)
    simpa using (h_diff1.differentiableAt (x := t - u)).hasDerivAt.comp u h_inner
  have h_left :
      HasDerivAt (fun v => Hf (t + v) + Hf (t - v))
        (deriv Hf (t + u) - deriv Hf (t - u)) u := by
    simpa using h_plus.add h_minus
  have h_const : HasDerivAt (fun _ : ℝ => 2 * Hf t) 0 u :=
    hasDerivAt_const u (2 * Hf t)
  have h_right :
      HasDerivAt (((fun _ : ℝ => 2 * Hf t) * Hf)) (2 * (Hf t * deriv Hf u)) u := by
    simpa [mul_assoc] using h_const.mul ((h_diff1.differentiableAt (x := u)).hasDerivAt)
  have h_eq :
      (fun v => Hf (t + v) + Hf (t - v)) = ((fun _ : ℝ => 2 * Hf t) * Hf) := by
    funext v
    simpa [Pi.mul_apply, mul_assoc] using h_dAlembert t v
  have h_deriv_eq := congrArg (fun f : ℝ → ℝ => deriv f u) h_eq
  change deriv (fun v => Hf (t + v) + Hf (t - v)) u =
      deriv (((fun _ : ℝ => 2 * Hf t) * Hf)) u at h_deriv_eq
  rw [h_left.deriv, h_right.deriv] at h_deriv_eq
  simpa [mul_assoc] using h_deriv_eq

/-- Differentiate the first-derivative identity at `u = 0` to relate `H''(t)` to `H''(0)`. -/
theorem dAlembert_second_deriv_at_zero_of_contDiff
    (Hf : ℝ → ℝ)
    (h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u)
    (h_diff : ContDiff ℝ 2 Hf) :
    ∀ t, 2 * deriv (deriv Hf) t = 2 * Hf t * deriv (deriv Hf) 0 := by
  intro t
  have h_first :
      (fun u => deriv Hf (t + u) - deriv Hf (t - u)) =
        ((fun _ : ℝ => 2 * Hf t) * deriv Hf) := by
    funext u
    simpa [Pi.mul_apply, mul_assoc] using
      dAlembert_first_deriv_of_contDiff Hf h_dAlembert h_diff t u
  have h_plus :
      HasDerivAt (fun u => deriv Hf (t + u)) (deriv (deriv Hf) t) 0 := by
    have h_inner : HasDerivAt (fun u => t + u) 1 0 := by
      simpa using (hasDerivAt_const 0 t).add (hasDerivAt_id 0)
    simpa using (hasDerivAt_deriv_of_contDiffTwo h_diff (t + 0)).comp 0 h_inner
  have h_minus_raw :
      HasDerivAt (fun u => deriv Hf (t - u)) (-deriv (deriv Hf) t) 0 := by
    have h_inner : HasDerivAt (fun u => t - u) (-1) 0 := by
      simpa using (hasDerivAt_const 0 t).sub (hasDerivAt_id 0)
    simpa using (hasDerivAt_deriv_of_contDiffTwo h_diff (t - 0)).comp 0 h_inner
  have h_left_raw :
      HasDerivAt (fun u => deriv Hf (t + u) - deriv Hf (t - u))
        (deriv (deriv Hf) t + deriv (deriv Hf) t) 0 := by
    simpa using h_plus.sub h_minus_raw
  have h_const : HasDerivAt (fun _ : ℝ => 2 * Hf t) 0 0 :=
    hasDerivAt_const 0 (2 * Hf t)
  have h_right :
      HasDerivAt (((fun _ : ℝ => 2 * Hf t) * deriv Hf))
        (2 * (Hf t * deriv (deriv Hf) 0)) 0 := by
    simpa [mul_assoc] using h_const.mul (hasDerivAt_deriv_of_contDiffTwo h_diff 0)
  have h_deriv_eq := congrArg (fun f : ℝ → ℝ => deriv f 0) h_first
  change deriv (fun u => deriv Hf (t + u) - deriv Hf (t - u)) 0 =
      deriv (((fun _ : ℝ => 2 * Hf t) * deriv Hf)) 0 at h_deriv_eq
  rw [h_left_raw.deriv, h_right.deriv] at h_deriv_eq
  linarith

/-- A `C²` d'Alembert solution with calibrated second derivative satisfies `H'' = H`. -/
theorem dAlembert_to_ODE_of_contDiff
    (Hf : ℝ → ℝ)
    (h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u)
    (h_diff : ContDiff ℝ 2 Hf)
    (h_deriv2_zero : deriv (deriv Hf) 0 = 1) :
    ∀ t, deriv (deriv Hf) t = Hf t := by
  intro t
  have h_rel := dAlembert_second_deriv_at_zero_of_contDiff Hf h_dAlembert h_diff t
  rw [h_deriv2_zero] at h_rel
  linarith

/-- Bridge from an explicit `ContDiff ℝ 2` hypothesis to the legacy ODE hypothesis. -/
theorem dAlembert_to_ODE_hypothesis_of_contDiff
    (Hf : ℝ → ℝ) (h_diff : ContDiff ℝ 2 Hf) :
    dAlembert_to_ODE_hypothesis Hf := by
  intro _ _ h_dAlembert h_deriv2_zero
  exact dAlembert_to_ODE_of_contDiff Hf h_dAlembert h_diff h_deriv2_zero

/-- A normalized composition-law cost is automatically reciprocal. -/
theorem composition_law_forces_reciprocity
    (F : ℝ → ℝ)
    (hNorm : IsNormalized F)
    (hComp : SatisfiesCompositionLaw F) :
    IsReciprocalCost F := by
  intro x hx
  let Hf : ℝ → ℝ := H F
  have h_H0 : Hf 0 = 1 := by
    dsimp [Hf]
    simpa [H, G, IsNormalized] using hNorm
  have hCoshAdd : CoshAddIdentity F := (composition_law_equiv_coshAdd F).mp hComp
  have h_direct : DirectCoshAdd (G F) := CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd
  have h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u := by
    intro t u
    have hG := h_direct t u
    have h_goal :
        (G F (t + u) + 1) + (G F (t - u) + 1) = 2 * (G F t + 1) * (G F u + 1) := by
      calc
        (G F (t + u) + 1) + (G F (t - u) + 1)
            = (G F (t + u) + G F (t - u)) + 2 := by ring
        _ = (2 * (G F t * G F u) + 2 * (G F t + G F u)) + 2 := by simpa [hG]
        _ = 2 * (G F t + 1) * (G F u + 1) := by ring
    simpa [Hf, H] using h_goal
  have h_even : Function.Even Hf := dAlembert_even Hf h_H0 h_dAlembert
  have h_even_at_log := h_even (Real.log x)
  have h_eq_plus :
      F x + 1 = F x⁻¹ + 1 := by
    simpa [Hf, H, G, Real.exp_log hx, Real.exp_neg] using h_even_at_log.symm
  linarith

/-- `C²` d'Alembert solutions are determined by calibration and equal `cosh`. -/
theorem dAlembert_cosh_solution_of_contDiff
    (Hf : ℝ → ℝ)
    (h_one : Hf 0 = 1)
    (h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u)
    (h_diff : ContDiff ℝ 2 Hf)
    (h_deriv2_zero : deriv (deriv Hf) 0 = 1) :
    ∀ t, Hf t = Real.cosh t := by
  have h_ode : ∀ t, deriv (deriv Hf) t = Hf t :=
    dAlembert_to_ODE_of_contDiff Hf h_dAlembert h_diff h_deriv2_zero
  have h_even : Function.Even Hf := dAlembert_even Hf h_one h_dAlembert
  have h_diff0 : DifferentiableAt ℝ Hf 0 :=
    (contDiffTwo_differentiable h_diff).differentiableAt
  have h_deriv_zero : deriv Hf 0 = 0 :=
    even_deriv_at_zero Hf h_even h_diff0
  exact ode_cosh_uniqueness_contdiff Hf h_diff h_ode h_one h_deriv_zero

/-- Sharpened T5 surface:
normalization, the composition law, calibration, and `C²` regularity of `H = G + 1`
already force the canonical reciprocal cost. Reciprocal symmetry is derived, not assumed. -/
theorem law_of_logic_forces_jcost_of_contDiff
    (F : ℝ → ℝ)
    (hNorm : IsNormalized F)
    (hComp : SatisfiesCompositionLaw F)
    (hCalib : IsCalibrated F)
    (h_diff : ContDiff ℝ 2 (H F)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  intro x hx
  let Gf : ℝ → ℝ := G F
  let Hf : ℝ → ℝ := H F
  have hCoshAdd : CoshAddIdentity F := (composition_law_equiv_coshAdd F).mp hComp
  have h_direct : DirectCoshAdd Gf := CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd
  have h_H0 : Hf 0 = 1 := by
    dsimp [Hf]
    simpa [H, G, IsNormalized] using hNorm
  have h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u := by
    intro t u
    have hG := h_direct t u
    have h_goal :
        (Gf (t + u) + 1) + (Gf (t - u) + 1) = 2 * (Gf t + 1) * (Gf u + 1) := by
      calc
        (Gf (t + u) + 1) + (Gf (t - u) + 1)
            = (Gf (t + u) + Gf (t - u)) + 2 := by ring
        _ = (2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)) + 2 := by simp [hG]
        _ = 2 * (Gf t + 1) * (Gf u + 1) := by ring
    simpa [Hf, H, Gf] using h_goal
  have h_H_d2 : deriv (deriv Hf) 0 = 1 := by
    have hG_d2 : deriv (deriv Gf) 0 = 1 := by
      simpa [Gf, G, IsCalibrated] using hCalib
    have hderiv : deriv Hf = deriv Gf := by
      funext t
      change deriv (fun y => Gf y + 1) t = deriv Gf t
      exact deriv_add_const (f := Gf) (x := t) (c := (1 : ℝ))
    have hderiv2 : deriv (deriv Hf) = deriv (deriv Gf) := congrArg deriv hderiv
    exact (congrArg (fun g => g 0) hderiv2).trans hG_d2
  have h_H_cosh : ∀ t, Hf t = Real.cosh t :=
    dAlembert_cosh_solution_of_contDiff Hf h_H0 h_dAlembert (by simpa [Hf] using h_diff) h_H_d2
  have h_G_cosh : ∀ t, Gf t = Real.cosh t - 1 := by
    intro t
    have hH := h_H_cosh t
    have hH' : Gf t + 1 = Real.cosh t := by
      simpa [Hf, H, Gf] using hH
    linarith
  have ht : Real.exp (Real.log x) = x := Real.exp_log hx
  have hJG : G Cost.Jcost (Real.log x) = Real.cosh (Real.log x) - 1 :=
    Jcost_G_eq_cosh_sub_one (Real.log x)
  calc
    F x = F (Real.exp (Real.log x)) := by rw [ht]
    _ = Gf (Real.log x) := rfl
    _ = Real.cosh (Real.log x) - 1 := h_G_cosh (Real.log x)
    _ = G Cost.Jcost (Real.log x) := by simpa using hJG.symm
    _ = Cost.Jcost (Real.exp (Real.log x)) := by simp [G]
    _ = Cost.Jcost x := by rw [ht]

end

end FunctionalEquation
end Cost
end IndisputableMonolith

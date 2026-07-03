import IndisputableMonolith.Cost.AczelProof
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Strict Functional-Equation Variants

This optional module tightens the T5 regularity surface without changing the
core theorem.  The theorem below replaces the explicit
`ContinuousOn F (Set.Ioi 0)` premise with limit-form log calibration, using the
already-proved d'Alembert continuity-from-log-curvature lemma.
-/

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

open Real

/-- Limit-form log calibration supplies the continuity needed by the Aczél
d'Alembert route, so the explicit `ContinuousOn F (Set.Ioi 0)` premise can be
removed from this T5 variant.  The derivative calibration is kept separately:
this theorem relaxes regularity, not the unit-setting datum. -/
theorem law_of_logic_forces_jcost_of_log_calibration (F : ℝ → ℝ)
    [AczelSmoothnessPackage]
    (_hRecip : IsReciprocalCost F)
    (hNorm : IsNormalized F)
    (hComp : SatisfiesCompositionLaw F)
    (hCalib : IsCalibrated F)
    (hLogCalib : IsCalibratedLimit F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  intro x hx
  have hCoshAdd : CoshAddIdentity F := (composition_law_equiv_coshAdd F).mp hComp
  let Gf : ℝ → ℝ := G F
  let Hf : ℝ → ℝ := H F
  have h_H0 : Hf 0 = 1 := by
    show H F 0 = 1
    simp only [H, G, Real.exp_zero]
    rw [hNorm]
    ring
  have h_direct : DirectCoshAdd Gf := CoshAddIdentity_implies_DirectCoshAdd F hCoshAdd
  have h_dAlembert : ∀ t u, Hf (t + u) + Hf (t - u) = 2 * Hf t * Hf u := by
    intro t u
    have hG := h_direct t u
    have h_goal :
        (Gf (t + u) + 1) + (Gf (t - u) + 1) =
          2 * (Gf t + 1) * (Gf u + 1) := by
      calc
        (Gf (t + u) + 1) + (Gf (t - u) + 1)
            = (Gf (t + u) + Gf (t - u)) + 2 := by ring
        _ = (2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)) + 2 := by simp [hG]
        _ = 2 * (Gf t + 1) * (Gf u + 1) := by ring
    simpa [Hf, H, Gf] using h_goal
  have h_log : HasLogCurvature Hf 1 := by
    simpa [Hf, IsCalibratedLimit] using hLogCalib
  have h_H_cont : Continuous Hf :=
    dAlembert_continuous_of_log_curvature Hf h_H0 h_dAlembert h_log
  have h_H_d2 : deriv (deriv Hf) 0 = 1 := by
    have hG_d2 : deriv (deriv Gf) 0 = 1 := by
      simpa [Gf, G] using hCalib
    have hderiv : deriv Hf = deriv Gf := by
      funext t
      change deriv (fun y => Gf y + 1) t = deriv Gf t
      exact deriv_add_const (f := Gf) (x := t) (c := (1 : ℝ))
    have hderiv2 : deriv (deriv Hf) = deriv (deriv Gf) := congrArg deriv hderiv
    exact (congrArg (fun g => g 0) hderiv2).trans hG_d2
  have h_H_cosh : ∀ t, Hf t = Real.cosh t :=
    dAlembert_cosh_solution_aczel Hf h_H0 h_H_cont h_dAlembert h_H_d2
  have h_G_cosh : ∀ t, Gf t = Real.cosh t - 1 := by
    intro t
    have hH : Gf t + 1 = Real.cosh t := by
      simpa [Hf, H, Gf] using h_H_cosh t
    linarith
  have ht : Real.exp (Real.log x) = x := Real.exp_log hx
  have hJG : G Cost.Jcost (Real.log x) = Real.cosh (Real.log x) - 1 :=
    Jcost_G_eq_cosh_sub_one (Real.log x)
  calc
    F x = F (Real.exp (Real.log x)) := by rw [ht]
    _ = Gf (Real.log x) := rfl
    _ = Real.cosh (Real.log x) - 1 := h_G_cosh (Real.log x)
    _ = G Cost.Jcost (Real.log x) := by simp only [hJG]
    _ = Cost.Jcost (Real.exp (Real.log x)) := by simp [G]
    _ = Cost.Jcost x := by simp [ht]

end FunctionalEquation
end Cost
end IndisputableMonolith

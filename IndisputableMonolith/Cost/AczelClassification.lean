import IndisputableMonolith.Cost.AczelTheorem
import IndisputableMonolith.Cost.AczelProof
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Cost
namespace FunctionalEquation

/-!
# Aczel Classification Package

This module packages the part of the d'Alembert forcing chain that is supplied
by the Aczel classification theorem:

1. continuous d'Alembert solutions are smooth;
2. once smoothness is available, the calibrated ODE kernel `H'' = H` follows.

The downstream exclusivity code can depend on this kernel without touching the
raw Aczel axiom directly.
-/

/-- The theorem-level payload extracted from the Aczel classification seam. -/
structure AczelRegularityKernel (H : ℝ → ℝ) : Prop where
  smooth : dAlembert_continuous_implies_smooth_hypothesis H
  ode : dAlembert_to_ODE_hypothesis H

/-- The default kernel obtained from the current Aczél smoothness package. -/
noncomputable def aczelRegularityKernel [AczelSmoothnessPackage] (H : ℝ → ℝ) :
    AczelRegularityKernel H where
  smooth := dAlembert_smooth_of_aczel H
  ode := by
    intro h_one h_cont h_dAlembert h_d2_zero
    have h_smooth : ContDiff ℝ ⊤ H :=
      dAlembert_smooth_of_aczel H h_one h_cont h_dAlembert
    exact dAlembert_to_ODE_theorem H h_smooth h_dAlembert h_d2_zero

/-- Convenience projection: the smoothness theorem exported by the kernel. -/
theorem aczel_kernel_smooth [AczelSmoothnessPackage] (H : ℝ → ℝ) :
    dAlembert_continuous_implies_smooth_hypothesis H :=
  (aczelRegularityKernel H).smooth

/-- Convenience projection: the ODE kernel exported by the classification step. -/
theorem aczel_kernel_ode [AczelSmoothnessPackage] (H : ℝ → ℝ) :
    dAlembert_to_ODE_hypothesis H :=
  (aczelRegularityKernel H).ode

/-- Canonical public T5 input bundle.

This is the primitive-to-uniqueness route exposed to the rest of the public RS
surface. `JensenSketch` remains available as a compatibility layer, but the
official statement now records the reciprocal-cost, normalization, composition,
calibration, and continuity assumptions explicitly. -/
structure PrimitiveCostHypotheses (F : ℝ → ℝ) : Prop where
  reciprocal : IsReciprocalCost F
  normalized : IsNormalized F
  composition : SatisfiesCompositionLaw F
  calibrated : IsCalibrated F
  continuous : ContinuousOn F (Set.Ioi 0)

private theorem H_one_of_normalized (F : ℝ → ℝ)
    (hNorm : IsNormalized F) : H F 0 = 1 := by
  have h0 : F 1 = 0 := by simpa [IsNormalized] using hNorm
  simp [H, G, h0]

private theorem H_continuous_of_positive_continuous (F : ℝ → ℝ)
    (hCont : ContinuousOn F (Set.Ioi 0)) : Continuous (H F) := by
  have h := ContinuousOn.comp_continuous hCont Real.continuous_exp
  have h' : Continuous (fun t => F (Real.exp t)) :=
    h (by intro t; exact Set.mem_Ioi.mpr (Real.exp_pos t))
  have h_add : Continuous (fun t : ℝ => F (Real.exp t) + (1 : ℝ)) :=
    h'.add (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
  simpa [H, G] using h_add

private theorem H_dAlembert_of_composition (F : ℝ → ℝ)
    (hComp : SatisfiesCompositionLaw F) :
    ∀ t u, H F (t + u) + H F (t - u) = 2 * H F t * H F u := by
  let Gf : ℝ → ℝ := G F
  have h_direct : DirectCoshAdd Gf :=
    CoshAddIdentity_implies_DirectCoshAdd F ((composition_law_equiv_coshAdd F).mp hComp)
  intro t u
  have hG := h_direct t u
  have h_goal : (Gf (t + u) + 1) + (Gf (t - u) + 1) = 2 * (Gf t + 1) * (Gf u + 1) := by
    calc
      (Gf (t + u) + 1) + (Gf (t - u) + 1)
          = (Gf (t + u) + Gf (t - u)) + 2 := by ring
      _ = (2 * (Gf t * Gf u) + 2 * (Gf t + Gf u)) + 2 := by
            simpa [Gf] using hG
      _ = 2 * (Gf t + 1) * (Gf u + 1) := by ring
  simpa [Gf, H, G] using h_goal

/-- Official public T5 theorem with an explicit Aczél kernel seam.

The public statement now takes the primitive cost hypotheses directly and uses
`AczelRegularityKernel` as the sole regularity bridge. This makes the T5 seam
explicit without routing through `JensenSketch`. -/
theorem primitive_to_uniqueness_of_kernel (F : ℝ → ℝ)
    (hF : PrimitiveCostHypotheses F)
    (hKernel : AczelRegularityKernel (H F)) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x := by
  have h_H0 : H F 0 = 1 := H_one_of_normalized F hF.normalized
  have h_H_cont : Continuous (H F) :=
    H_continuous_of_positive_continuous F hF.continuous
  have h_H_dAlembert : ∀ t u, H F (t + u) + H F (t - u) = 2 * H F t * H F u :=
    H_dAlembert_of_composition F hF.composition
  have h_smooth : ContDiff ℝ ⊤ (H F) :=
    hKernel.smooth h_H0 h_H_cont h_H_dAlembert
  exact law_of_logic_forces_jcost_with_regularization F
    hF.reciprocal hF.normalized hF.composition hF.calibrated hF.continuous
    hKernel.smooth hKernel.ode
    (ode_regularity_continuous_of_smooth h_smooth)
    (ode_regularity_differentiable_of_smooth h_smooth)
    (ode_regularity_bootstrap_of_smooth h_smooth)

/-- Convenience form of the canonical T5 theorem using the current Aczél
smoothness package to supply the regularity kernel automatically. -/
theorem primitive_to_uniqueness_aczel [AczelSmoothnessPackage] (F : ℝ → ℝ)
    (hF : PrimitiveCostHypotheses F) :
    ∀ x : ℝ, 0 < x → F x = Cost.Jcost x :=
  primitive_to_uniqueness_of_kernel F hF (aczelRegularityKernel (H F))

end FunctionalEquation
end Cost
end IndisputableMonolith

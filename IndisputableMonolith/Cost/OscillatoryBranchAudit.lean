import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

/-!
# Oscillatory Branch Audit for the Recognition Composition Law

This module records a peer-audit correction about the Recognition
Composition Law (RCL).  The RCL alone does not select the hyperbolic
branch.  In log coordinates, both

* `cosh t - 1`, and
* `cos t - 1`

satisfy the same d'Alembert addition law.  The oscillatory branch is
excluded by the RS side conditions: it has second log-derivative `-1` at
the origin and is negative for nonzero small log-ratios, so it fails the
unit positive calibration and the nonnegative-cost requirement.

This leaves the main cost uniqueness theorem unchanged.  It sharpens the
paper claim from "cos is incompatible with the RCL" to the correct statement:
"cos is an RCL branch, but calibration/positivity reject it."
-/

namespace IndisputableMonolith
namespace Cost
namespace OscillatoryBranchAudit

open FunctionalEquation

noncomputable section

/-- The oscillatory log branch pulled back to positive ratios. -/
noncomputable def oscillatoryCost (x : ℝ) : ℝ :=
  Real.cos (Real.log x) - 1

/-- In log coordinates the oscillatory branch is exactly `cos t - 1`. -/
@[simp] theorem G_oscillatoryCost (t : ℝ) :
    G oscillatoryCost t = Real.cos t - 1 := by
  simp [G, oscillatoryCost]

/-- The oscillatory branch satisfies the same shifted d'Alembert identity as `J`. -/
theorem oscillatory_cosh_add_identity :
    CoshAddIdentity oscillatoryCost := by
  intro t u
  simp only [G_oscillatoryCost]
  rw [Real.cos_add, Real.cos_sub]
  ring

/-- Therefore the oscillatory branch satisfies the RCL on positive ratios. -/
theorem oscillatory_satisfies_composition_law :
    SatisfiesCompositionLaw oscillatoryCost :=
  (composition_law_equiv_coshAdd oscillatoryCost).mpr
    oscillatory_cosh_add_identity

/-- The oscillatory branch is normalized at exact balance. -/
theorem oscillatory_normalized : IsNormalized oscillatoryCost := by
  simp [IsNormalized, oscillatoryCost]

/-- The oscillatory branch is reciprocal-symmetric. -/
theorem oscillatory_reciprocal : IsReciprocalCost oscillatoryCost := by
  intro x hx
  have hlog : Real.log x⁻¹ = - Real.log x := by
    simp [Real.log_inv]
  simp [oscillatoryCost, hlog, Real.cos_neg]

/-- Its second log-derivative at balance is `-1`, not `+1`. -/
theorem oscillatory_second_log_derivative :
    deriv (deriv (G oscillatoryCost)) 0 = -1 := by
  have hG : G oscillatoryCost = fun t => Real.cos t - 1 := by
    funext t
    exact G_oscillatoryCost t
  rw [hG]
  have hderiv : deriv (fun t : ℝ => Real.cos t - 1) =
      fun t => -Real.sin t := by
    funext t
    have hcos := Real.hasDerivAt_cos t
    have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
    simpa using (hcos.sub hconst).deriv
  have hderiv2 : deriv (fun t : ℝ => -Real.sin t) =
      fun t => -Real.cos t := by
    funext t
    have hsin := Real.hasDerivAt_sin t
    simpa using hsin.neg.deriv
  calc
    deriv (deriv (fun t : ℝ => Real.cos t - 1)) 0
        = deriv (fun t : ℝ => -Real.sin t) 0 := by rw [hderiv]
    _ = (fun t : ℝ => -Real.cos t) 0 := by rw [hderiv2]
    _ = -1 := by simp

/-- Hence it fails the RS unit calibration. -/
theorem oscillatory_not_calibrated :
    ¬ IsCalibrated oscillatoryCost := by
  intro h
  have hneg := oscillatory_second_log_derivative
  rw [IsCalibrated] at h
  linarith

/-- The oscillatory branch is negative at one nonzero log-ratio. -/
theorem oscillatory_negative_at_exp_pi :
    oscillatoryCost (Real.exp Real.pi) = -2 := by
  simp [oscillatoryCost]
  norm_num

/-- Consequently it is not a nonnegative recognition cost on positive ratios. -/
theorem oscillatory_not_nonnegative_on_positive :
    ¬ (∀ x : ℝ, 0 < x → 0 ≤ oscillatoryCost x) := by
  intro h
  have hpos : 0 < Real.exp Real.pi := Real.exp_pos Real.pi
  have hnonneg := h (Real.exp Real.pi) hpos
  rw [oscillatory_negative_at_exp_pi] at hnonneg
  norm_num at hnonneg

/-- Audit summary: RCL admits the oscillatory branch, but RS calibration and
nonnegativity reject it. -/
structure OscillatoryBranchCert where
  satisfies_rcl : SatisfiesCompositionLaw oscillatoryCost
  normalized : IsNormalized oscillatoryCost
  reciprocal : IsReciprocalCost oscillatoryCost
  second_log_derivative_eq_neg_one :
    deriv (deriv (G oscillatoryCost)) 0 = -1
  fails_calibration : ¬ IsCalibrated oscillatoryCost
  fails_nonnegativity :
    ¬ (∀ x : ℝ, 0 < x → 0 ≤ oscillatoryCost x)

/-- Certificate inhabitant for the oscillatory-branch audit. -/
theorem oscillatory_branch_audit : OscillatoryBranchCert where
  satisfies_rcl := oscillatory_satisfies_composition_law
  normalized := oscillatory_normalized
  reciprocal := oscillatory_reciprocal
  second_log_derivative_eq_neg_one := oscillatory_second_log_derivative
  fails_calibration := oscillatory_not_calibrated
  fails_nonnegativity := oscillatory_not_nonnegative_on_positive

end

end OscillatoryBranchAudit
end Cost
end IndisputableMonolith

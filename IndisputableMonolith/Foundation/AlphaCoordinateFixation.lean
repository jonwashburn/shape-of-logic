import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Foundation.DAlembert.WLOGAlphaOne

/-!
# Alpha-Coordinate Fixation: Higher-Derivative Calibration Forces J

The branch-selection theorem (`Foundation.BranchSelection`) reduces the
calibrated bilinear branch to the one-parameter family
\[
F_\alpha(x) = \frac{1}{\alpha^2}\bigl(\cosh(\alpha \ln x) - 1\bigr),
\qquad \alpha \geq 1.
\]
The unit log-curvature calibration `G''(0) = 1` is invariant under `α`
(see `Cost.costAlphaLog_unit_curvature`), so it does not pin `α`. The
companion paper `RS_Branch_Selection.tex` lists three candidate
fixations in §5; this module formalises **Option 2: higher-derivative
calibration**.

## The math

Let `G_α(t) := (1/α²)(cosh(αt) − 1)`. Then:

* `G_α'(t) = sinh(αt)/α` (already in `WLOGAlphaOne`).
* `G_α''(t) = cosh(αt)`, so `G_α''(0) = 1` for every `α`.
* `G_α'''(t) = α · sinh(αt)`, so `G_α'''(0) = 0`.
* `G_α^(4)(t) = α² · cosh(αt)`, so `G_α^(4)(0) = α²`.

The fourth-derivative calibration `G^(4)(0) = 1` therefore forces
`α² = 1`, and combined with `α ≥ 1` (the rigidity-paper convention),
gives `α = 1`. By `cost_alpha_one_eq_jcost`, this isolates the
canonical reciprocal cost `J(x) = (1/2)(x + x⁻¹) − 1`.

## Honest scope

This is one of three candidate `α`-fixation routes from §5 of the
branch paper. The other two (generator calibration `F(γ) = 1`,
action-functional minimisation) remain open, candidates for separate
modules. Option 2 is chosen here because the existing `IsCalibrated`
framework already routes through derivative-of-G calibration, so this
extension has the smallest infrastructure surface.
-/

namespace IndisputableMonolith
namespace Foundation
namespace AlphaCoordinateFixation

open Real
open IndisputableMonolith.Cost

noncomputable section

/-! ## Iterated derivative computations -/

/-- The first derivative of `CostAlphaLog α` is `sinh(αt) / α`. -/
private lemma hasDerivAt_costAlphaLog_first (α : ℝ) (hα : α ≠ 0) (t : ℝ) :
    HasDerivAt (CostAlphaLog α) (sinh (α * t) / α) t := by
  -- Recompute the proof from WLOGAlphaOne (private there).
  have h_inner : HasDerivAt (fun x : ℝ => α * x) α t := by
    have h : HasDerivAt (fun x => x * α) α t := by
      simpa using (hasDerivAt_id t).mul_const α
    rwa [show (fun x : ℝ => x * α) = (fun x => α * x) from
      funext fun x => mul_comm x α] at h
  have h1 : HasDerivAt (fun s => cosh (α * s)) (sinh (α * t) * α) t :=
    (hasDerivAt_cosh (α * t)).comp t h_inner
  have h2 : HasDerivAt (fun s => cosh (α * s) - 1) (sinh (α * t) * α) t :=
    h1.sub_const 1
  have h_const : HasDerivAt (fun _ : ℝ => (1 / α ^ 2 : ℝ)) 0 t :=
    hasDerivAt_const t (1 / α ^ 2)
  have h3 := h_const.mul h2
  simp only [zero_mul, zero_add] at h3
  unfold CostAlphaLog
  convert h3 using 1
  field_simp

private lemma deriv_costAlphaLog_eq (α : ℝ) (hα : α ≠ 0) :
    deriv (CostAlphaLog α) = fun t => sinh (α * t) / α :=
  funext fun t => (hasDerivAt_costAlphaLog_first α hα t).deriv

/-- The second derivative of `CostAlphaLog α` is `cosh(αt)`. -/
private lemma hasDerivAt_costAlphaLog_second (α : ℝ) (hα : α ≠ 0) (t : ℝ) :
    HasDerivAt (deriv (CostAlphaLog α)) (cosh (α * t)) t := by
  rw [deriv_costAlphaLog_eq α hα]
  have h_inner : HasDerivAt (fun x : ℝ => α * x) α t := by
    have h : HasDerivAt (fun x => x * α) α t := by
      simpa using (hasDerivAt_id t).mul_const α
    rwa [show (fun x : ℝ => x * α) = (fun x => α * x) from
      funext fun x => mul_comm x α] at h
  have h1 : HasDerivAt (fun s => sinh (α * s)) (cosh (α * t) * α) t :=
    (hasDerivAt_sinh (α * t)).comp t h_inner
  convert h1.div_const α using 1
  field_simp

private lemma deriv_deriv_costAlphaLog_eq (α : ℝ) (hα : α ≠ 0) :
    deriv (deriv (CostAlphaLog α)) = fun t => cosh (α * t) :=
  funext fun t => (hasDerivAt_costAlphaLog_second α hα t).deriv

/-- The third derivative of `CostAlphaLog α` is `α · sinh(αt)`. -/
private lemma hasDerivAt_costAlphaLog_third (α : ℝ) (hα : α ≠ 0) (t : ℝ) :
    HasDerivAt (deriv (deriv (CostAlphaLog α))) (α * sinh (α * t)) t := by
  rw [deriv_deriv_costAlphaLog_eq α hα]
  have h_inner : HasDerivAt (fun x : ℝ => α * x) α t := by
    have h : HasDerivAt (fun x => x * α) α t := by
      simpa using (hasDerivAt_id t).mul_const α
    rwa [show (fun x : ℝ => x * α) = (fun x => α * x) from
      funext fun x => mul_comm x α] at h
  have h1 : HasDerivAt (fun s => cosh (α * s)) (sinh (α * t) * α) t :=
    (hasDerivAt_cosh (α * t)).comp t h_inner
  convert h1 using 1
  ring

private lemma deriv_deriv_deriv_costAlphaLog_eq (α : ℝ) (hα : α ≠ 0) :
    deriv (deriv (deriv (CostAlphaLog α))) = fun t => α * sinh (α * t) :=
  funext fun t => (hasDerivAt_costAlphaLog_third α hα t).deriv

/-- The fourth derivative of `CostAlphaLog α` is `α² · cosh(αt)`. -/
private lemma hasDerivAt_costAlphaLog_fourth (α : ℝ) (hα : α ≠ 0) (t : ℝ) :
    HasDerivAt (deriv (deriv (deriv (CostAlphaLog α))))
      (α ^ 2 * cosh (α * t)) t := by
  rw [deriv_deriv_deriv_costAlphaLog_eq α hα]
  have h_inner : HasDerivAt (fun x : ℝ => α * x) α t := by
    have h : HasDerivAt (fun x => x * α) α t := by
      simpa using (hasDerivAt_id t).mul_const α
    rwa [show (fun x : ℝ => x * α) = (fun x => α * x) from
      funext fun x => mul_comm x α] at h
  have h1 : HasDerivAt (fun s => sinh (α * s)) (cosh (α * t) * α) t :=
    (hasDerivAt_sinh (α * t)).comp t h_inner
  have h2 : HasDerivAt (fun s => α * sinh (α * s))
      (α * (cosh (α * t) * α)) t :=
    h1.const_mul α
  convert h2 using 1
  ring

/-! ## Headline derivative theorem -/

/-- **The fourth derivative of `CostAlphaLog α` at zero is `α²`.**

This is the calibration invariant that distinguishes different `α` values
within the bilinear family: the second derivative `G_α''(0) = 1` is
constant, but the fourth derivative `G_α^(4)(0) = α²` separates them. -/
theorem costAlphaLog_fourth_deriv_at_zero (α : ℝ) (hα : α ≠ 0) :
    deriv (deriv (deriv (deriv (CostAlphaLog α)))) 0 = α ^ 2 := by
  have := (hasDerivAt_costAlphaLog_fourth α hα 0).deriv
  rw [this]
  simp [mul_zero, cosh_zero]

/-! ## High calibration -/

/-- **Higher-derivative calibration**: a cost function in log coordinates
satisfies `G^(4)(0) = 1`. -/
def IsHighCalibratedLog (G : ℝ → ℝ) : Prop :=
  deriv (deriv (deriv (deriv G))) 0 = 1

/-- The α-cost is high-calibrated iff `α² = 1`. -/
theorem costAlphaLog_high_calibrated_iff (α : ℝ) (hα : α ≠ 0) :
    IsHighCalibratedLog (CostAlphaLog α) ↔ α ^ 2 = 1 := by
  unfold IsHighCalibratedLog
  rw [costAlphaLog_fourth_deriv_at_zero α hα]

/-! ## The α-pin -/

/-- **The α-pin theorem.** Within the bilinear `α`-family with the
rigidity-paper convention `α ≥ 1`, higher-derivative calibration forces
`α = 1`. -/
theorem alpha_pin_under_high_calibration
    (α : ℝ) (h_pos : 1 ≤ α)
    (h_calib : IsHighCalibratedLog (CostAlphaLog α)) :
    α = 1 := by
  have hα_ne : α ≠ 0 := by linarith
  have hα_sq : α ^ 2 = 1 :=
    (costAlphaLog_high_calibrated_iff α hα_ne).mp h_calib
  -- α ≥ 1 and α² = 1 forces α = 1.
  nlinarith

/-! ## J is the unique high-calibrated bilinear cost -/

/-- The `α = 1` bilinear cost is exactly `Jcost`. -/
theorem alpha_pinned_to_one_implies_J (x : ℝ) (hx : 0 < x) :
    CostAlpha 1 x = Jcost x :=
  cost_alpha_one_eq_jcost x hx

/-- **The full uniqueness theorem.** Within the bilinear `α`-family,
under the convention `α ≥ 1`, higher-derivative calibration forces
`α = 1`, and the cost on positive reals is exactly `Jcost`. -/
theorem J_uniquely_calibrated_via_higher_derivative
    (α : ℝ) (h_pos : 1 ≤ α)
    (h_calib : IsHighCalibratedLog (CostAlphaLog α)) :
    ∀ x : ℝ, 0 < x → CostAlpha α x = Jcost x := by
  intro x hx
  have hα_eq : α = 1 := alpha_pin_under_high_calibration α h_pos h_calib
  rw [hα_eq]
  exact cost_alpha_one_eq_jcost x hx

/-! ## Headline Certificate -/

/-- **Alpha-Coordinate Fixation Certificate.**

Within the bilinear branch produced by `BranchSelection`, the fourth-derivative
calibration `G^(4)(0) = 1` pins `α = 1` (under the convention `α ≥ 1`),
isolating `J` as the unique calibrated cost. -/
structure AlphaCoordinateFixationCert where
  fourth_deriv_eq_alpha_sq :
    ∀ α : ℝ, α ≠ 0 →
      deriv (deriv (deriv (deriv (CostAlphaLog α)))) 0 = α ^ 2
  high_calibrated_iff :
    ∀ α : ℝ, α ≠ 0 →
      (IsHighCalibratedLog (CostAlphaLog α) ↔ α ^ 2 = 1)
  alpha_pin :
    ∀ α : ℝ, 1 ≤ α →
      IsHighCalibratedLog (CostAlphaLog α) → α = 1
  alpha_one_is_J :
    ∀ x : ℝ, 0 < x → CostAlpha 1 x = Jcost x
  J_unique_under_high_calibration :
    ∀ α : ℝ, 1 ≤ α →
      IsHighCalibratedLog (CostAlphaLog α) →
      ∀ x : ℝ, 0 < x → CostAlpha α x = Jcost x

def alphaCoordinateFixationCert : AlphaCoordinateFixationCert where
  fourth_deriv_eq_alpha_sq := costAlphaLog_fourth_deriv_at_zero
  high_calibrated_iff := costAlphaLog_high_calibrated_iff
  alpha_pin := alpha_pin_under_high_calibration
  alpha_one_is_J := alpha_pinned_to_one_implies_J
  J_unique_under_high_calibration := J_uniquely_calibrated_via_higher_derivative

theorem alphaCoordinateFixationCert_inhabited :
    Nonempty AlphaCoordinateFixationCert :=
  ⟨alphaCoordinateFixationCert⟩

end

/-! ## Summary

The branch-selection chain now reads:

```
RCL family (translation theorem)
   ↓ branch selection (BranchSelection.lean)
bilinear α-family with α ≥ 1
   ↓ second-derivative calibration (constant in α: blind)
   ↓ fourth-derivative calibration (this module)
α = 1, hence F = J
```

`J` is now the unique calibrated cost on the bilinear branch under the
combined operator-level encoding plus the higher-derivative calibration.
The α-coordinate freedom is closed.

The other two §5 candidate fixations (generator calibration,
action-functional minimisation) remain open as alternative routes for
separate modules, but the present module gives one Lean-backed route to
canonical J.
-/

end AlphaCoordinateFixation
end Foundation
end IndisputableMonolith

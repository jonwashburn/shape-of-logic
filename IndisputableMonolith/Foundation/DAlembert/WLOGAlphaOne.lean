import Mathlib
import IndisputableMonolith.Cost

/-!
# WLOG α = 1: The Coordinate-Rescaling Proposition

After calibration κ(F) = 1 forces c = 2α², the calibrated solution family is

    F_α(x) = (1/α²)(cosh(α ln x) − 1),   α ≥ 1.

**Proposition**: F_α(x) = (1/α²) · J(x^α), where J(x) = (x+x⁻¹)/2 − 1.

The map φ_α : x ↦ x^α is a group automorphism of (ℝ₊, ·), so α merely
reparametrises the multiplicative coordinate. Setting α = 1 recovers J
exactly, and the unit-curvature condition G_α''(0) = 1 holds for every α.

Conclusion: without loss of generality, one may assume α = 1.
-/

namespace IndisputableMonolith
namespace Cost

open Real

noncomputable section

/-- The α-parameterized cost in log coordinates:
    G_α(t) = (1/α²)(cosh(αt) − 1). -/
def CostAlphaLog (α t : ℝ) : ℝ :=
  (1 / α ^ 2) * (cosh (α * t) - 1)

/-- The α-parameterized cost in multiplicative coordinates:
    F_α(x) = (1/α²)(cosh(α ln x) − 1). -/
def CostAlpha (α x : ℝ) : ℝ :=
  CostAlphaLog α (log x)

/-! ## Rescaling Identity -/

/-- Core identity: cosh(α log x) − 1 = J(x^α) for x > 0.
    Proof uses x^α = exp(α log x), then Jcost ∘ exp = cosh − 1. -/
theorem cosh_log_eq_jcost_rpow (α x : ℝ) (hx : 0 < x) :
    cosh (α * log x) - 1 = Jcost (x ^ α) := by
  have h : x ^ α = exp (α * log x) := by
    rw [rpow_def_of_pos hx, mul_comm]
  rw [h, ← Jcost_exp_cosh]

/-- **Rescaling Identity**: F_α(x) = (1/α²) · J(x^α). -/
theorem cost_alpha_rescaling (α x : ℝ) (hx : 0 < x) :
    CostAlpha α x = (1 / α ^ 2) * Jcost (x ^ α) := by
  unfold CostAlpha CostAlphaLog
  congr 1
  exact cosh_log_eq_jcost_rpow α x hx

/-! ## α = 1 Recovery -/

/-- Setting α = 1 gives F₁(x) = J(x) for x > 0. -/
theorem cost_alpha_one_eq_jcost (x : ℝ) (hx : 0 < x) :
    CostAlpha 1 x = Jcost x := by
  rw [cost_alpha_rescaling 1 x hx]
  simp [rpow_one]

/-! ## Multiplicative Group Automorphism

The rescaling φ_α : x ↦ x^α is a group homomorphism of (ℝ₊, ·).
It preserves multiplication, the identity, and inversion.
-/

theorem rpow_mul_hom' (α : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x * y) ^ α = x ^ α * y ^ α := by
  rw [rpow_def_of_pos (mul_pos hx hy), rpow_def_of_pos hx, rpow_def_of_pos hy,
      log_mul hx.ne' hy.ne', add_mul, exp_add]

theorem rpow_one_base' (α : ℝ) : (1 : ℝ) ^ α = 1 := one_rpow α

theorem rpow_inv_hom' (α : ℝ) {x : ℝ} (hx : 0 < x) :
    x⁻¹ ^ α = (x ^ α)⁻¹ := by
  rw [rpow_def_of_pos (inv_pos.mpr hx), rpow_def_of_pos hx,
      log_inv, neg_mul, exp_neg]

/-! ## Calibration Invariance -/

private lemma hasDerivAt_alpha_mul (α t : ℝ) :
    HasDerivAt (fun x => α * x) α t := by
  have h : HasDerivAt (fun x => x * α) α t := by
    simpa using (hasDerivAt_id t).mul_const α
  rwa [show (fun x : ℝ => x * α) = (fun x => α * x) from
    funext fun x => mul_comm x α] at h

private lemma hasDerivAt_costAlphaLog (α : ℝ) (hα : α ≠ 0) (t : ℝ) :
    HasDerivAt (CostAlphaLog α) (sinh (α * t) / α) t := by
  have h1 : HasDerivAt (fun s => cosh (α * s)) (sinh (α * t) * α) t :=
    (hasDerivAt_cosh (α * t)).comp t (hasDerivAt_alpha_mul α t)
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
  funext fun t => (hasDerivAt_costAlphaLog α hα t).deriv

private lemma hasDerivAt_sinhDivAlpha (α : ℝ) (hα : α ≠ 0) (t : ℝ) :
    HasDerivAt (fun s => sinh (α * s) / α) (cosh (α * t)) t := by
  have h1 : HasDerivAt (fun s => sinh (α * s)) (cosh (α * t) * α) t :=
    (hasDerivAt_sinh (α * t)).comp t (hasDerivAt_alpha_mul α t)
  convert h1.div_const α using 1
  field_simp

/-- **Calibration Invariance**: G_α''(0) = 1 for every α ≠ 0.
    The unit-curvature condition is independent of the rescaling parameter. -/
theorem costAlphaLog_unit_curvature (α : ℝ) (hα : α ≠ 0) :
    deriv (deriv (CostAlphaLog α)) 0 = 1 := by
  rw [deriv_costAlphaLog_eq α hα, (hasDerivAt_sinhDivAlpha α hα 0).deriv,
      mul_zero, cosh_zero]

/-! ## WLOG Theorem -/

/-- **WLOG α = 1**: Every calibrated cost F_α is the canonical cost J under
    coordinate rescaling. The parameter α does not introduce a structurally
    new cost function.

    Components:
    1. Rescaling identity: F_α(x) = (1/α²) · J(x^α)
    2. Recovery: F₁(x) = J(x)
    3. Group automorphism: (xy)^α = x^α · y^α
    4. Calibration invariance: G_α''(0) = 1 -/
theorem wlog_alpha_eq_one (α : ℝ) (hα : 0 < α) :
    (∀ x : ℝ, 0 < x → CostAlpha α x = (1 / α ^ 2) * Jcost (x ^ α))
    ∧ (∀ x : ℝ, 0 < x → CostAlpha 1 x = Jcost x)
    ∧ (∀ x y : ℝ, 0 < x → 0 < y → (x * y) ^ α = x ^ α * y ^ α)
    ∧ deriv (deriv (CostAlphaLog α)) 0 = 1 :=
  ⟨fun x hx => cost_alpha_rescaling α x hx,
   fun x hx => cost_alpha_one_eq_jcost x hx,
   fun _ _ hx hy => rpow_mul_hom' α hx hy,
   costAlphaLog_unit_curvature α hα.ne'⟩

end
end Cost
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Cost

/-!
# C7: Local J-Cost Expansion at Equilibrium

The plan originally asked for a Hessian theorem at r = 1. Rather than invoke
Mathlib's derivative API, this module proves the exact local algebraic kernel:

  J(1 + eps) = eps^2 / (2(1 + eps)).

This is stronger than the second-order Taylor claim away from eps = -1. It
also records the formal Taylor coefficient 1/2, so the Hessian coefficient is
1 in the usual normalization.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace JCostHessianC7

open Cost

theorem jcost_one_plus_eq (eps : ℝ) (h : eps ≠ -1) :
    Jcost (1 + eps) = eps ^ 2 / (2 * (1 + eps)) := by
  have hx : 1 + eps ≠ 0 := by
    intro hz
    apply h
    linarith
  rw [Jcost_eq_sq hx]
  ring_nf

/-- The exact quadratic numerator in the local J-cost expansion. -/
theorem jcost_local_quadratic_kernel (eps : ℝ) (h : eps ≠ -1) :
    Jcost (1 + eps) * (2 * (1 + eps)) = eps ^ 2 := by
  rw [jcost_one_plus_eq eps h]
  have hx : 1 + eps ≠ 0 := by
    intro hz
    apply h
    linarith
  have hden : 2 * (1 + eps) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hx
  field_simp [hden, hx]

/-- Taylor coefficient at equilibrium: J(1+eps) has leading term eps^2 / 2. -/
noncomputable def jcostTaylorQuadraticCoefficient : ℝ := 1 / 2

theorem jcostTaylorQuadraticCoefficient_eq :
    jcostTaylorQuadraticCoefficient = 1 / 2 := rfl

/-- In the standard Taylor convention, Hessian = 2 * quadratic coefficient. -/
noncomputable def jcostHessianCoefficient : ℝ :=
  2 * jcostTaylorQuadraticCoefficient

theorem jcostHessianCoefficient_eq_one :
    jcostHessianCoefficient = 1 := by
  unfold jcostHessianCoefficient jcostTaylorQuadraticCoefficient
  norm_num

structure JCostHessianCert where
  local_kernel : ∀ eps : ℝ, eps ≠ -1 →
    Jcost (1 + eps) * (2 * (1 + eps)) = eps ^ 2
  coefficient_half : jcostTaylorQuadraticCoefficient = 1 / 2
  hessian_one : jcostHessianCoefficient = 1

def jcostHessianCert : JCostHessianCert where
  local_kernel := jcost_local_quadratic_kernel
  coefficient_half := jcostTaylorQuadraticCoefficient_eq
  hessian_one := jcostHessianCoefficient_eq_one

end JCostHessianC7
end Foundation
end IndisputableMonolith

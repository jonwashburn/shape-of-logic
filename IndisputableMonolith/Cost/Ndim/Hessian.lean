import IndisputableMonolith.Cost.Ndim.Core

/-!
# Hessian formulas for the `n`-dimensional reciprocal cost

This module exposes the public replacement for the missing private
`IndisputableMonolith.Cost.Ndim.Hessian` file referenced by
`Metric.lean`.

The key point is that in log-coordinates the `n`-dimensional cost
depends only on the single weighted aggregate `dot α t`, so its Hessian
is rank one and factors through the outer product `α ⊗ α`.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators

/-- Log-coordinate gradient entry for `JlogN`. -/
noncomputable def gradientEntry {n : ℕ} (α t : Vec n) (i : Fin n) : ℝ :=
  α i * Real.sinh (dot α t)

/-- Log-coordinate Hessian entry for `JlogN`. -/
noncomputable def hessianEntry {n : ℕ} (α t : Vec n) (i j : Fin n) : ℝ :=
  α i * α j * Real.cosh (dot α t)

/-- The equilibrium Hessian model is the outer product `α ⊗ α`. -/
def hessianMatrix {n : ℕ} (α : Vec n) : Fin n → Fin n → ℝ :=
  fun i j => α i * α j

/-- The Hessian matrix at an arbitrary log-state. -/
noncomputable def hessianAt {n : ℕ} (α t : Vec n) : Fin n → Fin n → ℝ :=
  fun i j => hessianEntry α t i j

/-- Apply a tensor written in coordinates to a vector. -/
noncomputable def applyTensor {n : ℕ}
    (H : Fin n → Fin n → ℝ) (v : Vec n) : Vec n :=
  fun i => ∑ j : Fin n, H i j * v j

/-- The action of the log-coordinate Hessian on a vector. -/
noncomputable def applyHessian {n : ℕ} (α t v : Vec n) : Vec n :=
  applyTensor (hessianAt α t) v

/-- Quadratic form associated with the Hessian. -/
noncomputable def quadraticHessian {n : ℕ} (α t v : Vec n) : ℝ :=
  dot v (applyHessian α t v)

@[simp] theorem hessianEntry_zero {n : ℕ} (α : Vec n) (i j : Fin n) :
    hessianEntry α (fun _ => 0) i j = α i * α j := by
  unfold hessianEntry dot
  simp [Real.cosh_zero]

@[simp] theorem hessianAt_zero {n : ℕ} (α : Vec n) :
    hessianAt α (fun _ => 0) = hessianMatrix α := by
  funext i j
  simp [hessianAt, hessianMatrix, hessianEntry_zero]

/-- The full Hessian is a scalar multiple of the equilibrium outer-product model. -/
theorem hessianAt_factor {n : ℕ} (α t : Vec n) :
    hessianAt α t = fun i j => Real.cosh (dot α t) * hessianMatrix α i j := by
  funext i j
  unfold hessianAt hessianEntry hessianMatrix
  ring

/-- The Hessian action is always parallel to `α`. -/
theorem applyHessian_eq_direction {n : ℕ} (α t v : Vec n) :
    applyHessian α t v = fun i => Real.cosh (dot α t) * α i * dot α v := by
  funext i
  unfold applyHessian applyTensor hessianAt hessianEntry dot
  calc
    ∑ j : Fin n, (α i * α j * Real.cosh (dot α t)) * v j
        = ∑ j : Fin n, (α i * Real.cosh (dot α t)) * (α j * v j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = (α i * Real.cosh (dot α t)) * ∑ j : Fin n, α j * v j := by
          rw [Finset.mul_sum]
    _ = Real.cosh (dot α t) * α i * dot α v := by
          simp [dot, mul_comm, mul_assoc]

/-- Vectors orthogonal to `α` lie in the kernel of the Hessian. -/
theorem applyHessian_of_dot_zero {n : ℕ} (α t v : Vec n)
    (hv : dot α v = 0) :
    applyHessian α t v = 0 := by
  funext i
  simp [applyHessian_eq_direction, hv]

/-- The Hessian quadratic form depends only on the single active direction `dot α v`. -/
theorem quadraticHessian_eq {n : ℕ} (α t v : Vec n) :
    quadraticHessian α t v = Real.cosh (dot α t) * (dot α v) ^ 2 := by
  unfold quadraticHessian dot
  rw [applyHessian_eq_direction]
  calc
    ∑ i : Fin n, v i * (Real.cosh (dot α t) * α i * dot α v)
        = ∑ i : Fin n, Real.cosh (dot α t) * dot α v * (v i * α i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = (Real.cosh (dot α t) * dot α v) * ∑ i : Fin n, v i * α i := by
          rw [Finset.mul_sum]
    _ = Real.cosh (dot α t) * (dot α v) * dot α v := by
          congr 1
          unfold dot
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = Real.cosh (dot α t) * (dot α v) ^ 2 := by
          ring

theorem quadraticHessian_nonneg {n : ℕ} (α t v : Vec n) :
    0 ≤ quadraticHessian α t v := by
  rw [quadraticHessian_eq]
  positivity

end Ndim
end Cost
end IndisputableMonolith

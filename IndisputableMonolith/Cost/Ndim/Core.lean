import Mathlib
import IndisputableMonolith.Cost

/-!
# N-dimensional reciprocal cost: core definitions

This module defines the multi-component reciprocal cost by lifting the scalar
kernel through a weighted log aggregate.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators

/-- `n`-component real vectors as coordinate functions. -/
abbrev Vec (n : ℕ) := Fin n → ℝ

/-- Weighted dot product used by the logarithmic aggregate. -/
def dot {n : ℕ} (α t : Vec n) : ℝ := ∑ i : Fin n, α i * t i

/-- Componentwise logarithm. -/
noncomputable def logVec {n : ℕ} (x : Vec n) : Vec n := fun i => Real.log (x i)

/-- Componentwise multiplication. -/
def hadamardMul {n : ℕ} (x y : Vec n) : Vec n := fun i => x i * y i

/-- Componentwise inversion. -/
noncomputable def hadamardInv {n : ℕ} (x : Vec n) : Vec n := fun i => (x i)⁻¹

/-- Componentwise division. -/
noncomputable def hadamardDiv {n : ℕ} (x y : Vec n) : Vec n := fun i => x i / y i

/-- Exponential aggregate `R(x) = exp(∑ αᵢ log xᵢ)`. -/
noncomputable def aggregate {n : ℕ} (α x : Vec n) : ℝ :=
  Real.exp (dot α (logVec x))

/-- Log-coordinate `n`-dimensional cost. -/
noncomputable def JlogN {n : ℕ} (α t : Vec n) : ℝ :=
  Jcost (Real.exp (dot α t))

/-- Original positive-coordinate `n`-dimensional cost. -/
noncomputable def JcostN {n : ℕ} (α x : Vec n) : ℝ :=
  JlogN α (logVec x)

@[simp] theorem aggregate_pos {n : ℕ} (α x : Vec n) : 0 < aggregate α x := by
  unfold aggregate
  exact Real.exp_pos _

@[simp] theorem JcostN_eq_Jcost_aggregate {n : ℕ} (α x : Vec n) :
    JcostN α x = Jcost (aggregate α x) := by
  rfl

theorem JlogN_eq_cosh_sub_one {n : ℕ} (α t : Vec n) :
    JlogN α t = Real.cosh (dot α t) - 1 := by
  simpa [JlogN] using (Jcost_exp_cosh (dot α t))

theorem JcostN_eq_cosh_logsum {n : ℕ} (α x : Vec n) :
    JcostN α x = Real.cosh (dot α (logVec x)) - 1 := by
  simpa [JcostN, JlogN] using (Jcost_exp_cosh (dot α (logVec x)))

/-- Normalization at the identity vector. -/
theorem JcostN_unit {n : ℕ} (α : Vec n) :
    JcostN α (fun _ => 1) = 0 := by
  simp [JcostN, JlogN, dot, logVec, Jcost_unit0]

/-- Non-negativity follows from scalar non-negativity at positive aggregate. -/
theorem JcostN_nonneg {n : ℕ} (α x : Vec n) : 0 ≤ JcostN α x := by
  rw [JcostN_eq_Jcost_aggregate]
  exact Jcost_nonneg (aggregate_pos α x)

/-- Log-aggregate of a componentwise product. -/
theorem dot_log_hadamardMul {n : ℕ} (α x y : Vec n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    dot α (logVec (hadamardMul x y)) = dot α (logVec x) + dot α (logVec y) := by
  unfold dot logVec hadamardMul
  calc
    ∑ i : Fin n, α i * Real.log (x i * y i)
        = ∑ i : Fin n, α i * (Real.log (x i) + Real.log (y i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Real.log_mul (show x i ≠ 0 from (hx i).ne') (show y i ≠ 0 from (hy i).ne')]
    _ = ∑ i : Fin n, (α i * Real.log (x i) + α i * Real.log (y i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = (∑ i : Fin n, α i * Real.log (x i)) + (∑ i : Fin n, α i * Real.log (y i)) := by
          simpa using Finset.sum_add_distrib

/-- Log-aggregate of a componentwise quotient. -/
theorem dot_log_hadamardDiv {n : ℕ} (α x y : Vec n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    dot α (logVec (hadamardDiv x y)) = dot α (logVec x) - dot α (logVec y) := by
  unfold dot logVec hadamardDiv
  calc
    ∑ i : Fin n, α i * Real.log (x i / y i)
        = ∑ i : Fin n, α i * (Real.log (x i) - Real.log (y i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Real.log_div (show x i ≠ 0 from (hx i).ne') (show y i ≠ 0 from (hy i).ne')]
    _ = ∑ i : Fin n, (α i * Real.log (x i) - α i * Real.log (y i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = (∑ i : Fin n, α i * Real.log (x i)) - (∑ i : Fin n, α i * Real.log (y i)) := by
          simp [Finset.sum_sub_distrib]

/-- Log-aggregate of a componentwise inverse. -/
theorem dot_log_hadamardInv {n : ℕ} (α x : Vec n) :
    dot α (logVec (hadamardInv x)) = - dot α (logVec x) := by
  unfold dot logVec hadamardInv
  calc
    ∑ i : Fin n, α i * Real.log ((x i)⁻¹)
        = ∑ i : Fin n, α i * (-Real.log (x i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Real.log_inv]
    _ = ∑ i : Fin n, -(α i * Real.log (x i)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
    _ = - (∑ i : Fin n, α i * Real.log (x i)) := by
          simp

/-- Reciprocity under componentwise inversion. -/
theorem JcostN_reciprocal {n : ℕ} (α x : Vec n) :
    JcostN α (hadamardInv x) = JcostN α x := by
  rw [JcostN_eq_cosh_logsum, JcostN_eq_cosh_logsum]
  rw [dot_log_hadamardInv, Real.cosh_neg]

/-- Zero-cost characterization in log coordinates. -/
theorem JcostN_eq_zero_iff {n : ℕ} (α x : Vec n) :
    JcostN α x = 0 ↔ dot α (logVec x) = 0 := by
  unfold JcostN JlogN
  simpa [Jlog] using (Jlog_eq_zero_iff (t := dot α (logVec x)))

end Ndim
end Cost
end IndisputableMonolith

import IndisputableMonolith.Cost.Ndim.Core

/-!
# Multidimensional d'Alembert / RCL identity
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

theorem JcostN_dAlembert {n : ℕ} (α x y : Vec n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    JcostN α (hadamardMul x y) + JcostN α (hadamardDiv x y)
      = 2 * JcostN α x + 2 * JcostN α y + 2 * JcostN α x * JcostN α y := by
  let u : ℝ := Real.exp (dot α (logVec x))
  let v : ℝ := Real.exp (dot α (logVec y))
  have hu : 0 < u := by
    dsimp [u]
    exact Real.exp_pos _
  have hv : 0 < v := by
    dsimp [v]
    exact Real.exp_pos _
  have hmul :
      JcostN α (hadamardMul x y) = Jcost (u * v) := by
    calc
      JcostN α (hadamardMul x y)
          = Jcost (Real.exp (dot α (logVec (hadamardMul x y)))) := by
              simp [JcostN, JlogN]
      _ = Jcost (Real.exp (dot α (logVec x) + dot α (logVec y))) := by
            rw [dot_log_hadamardMul α x y hx hy]
      _ = Jcost (u * v) := by
            simp [u, v, Real.exp_add]
  have hdiv :
      JcostN α (hadamardDiv x y) = Jcost (u / v) := by
    calc
      JcostN α (hadamardDiv x y)
          = Jcost (Real.exp (dot α (logVec (hadamardDiv x y)))) := by
              simp [JcostN, JlogN]
      _ = Jcost (Real.exp (dot α (logVec x) - dot α (logVec y))) := by
            rw [dot_log_hadamardDiv α x y hx hy]
      _ = Jcost (u / v) := by
            simp [u, v, Real.exp_sub]
  have hbase := dalembert_identity (x := u) (y := v) hu hv
  calc
    JcostN α (hadamardMul x y) + JcostN α (hadamardDiv x y)
        = Jcost (u * v) + Jcost (u / v) := by rw [hmul, hdiv]
    _ = 2 * Jcost u + 2 * Jcost v + 2 * Jcost u * Jcost v := hbase
    _ = 2 * JcostN α x + 2 * JcostN α y + 2 * JcostN α x * JcostN α y := by
          simp [u, v, JcostN, JlogN]

lemma JcostN_submult {n : ℕ} (α x y : Vec n)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    JcostN α (hadamardMul x y)
      ≤ 2 * JcostN α x + 2 * JcostN α y + 2 * JcostN α x * JcostN α y := by
  have h := JcostN_dAlembert α x y hx hy
  have hnonneg : 0 ≤ JcostN α (hadamardDiv x y) := JcostN_nonneg α (hadamardDiv x y)
  linarith

end Ndim
end Cost
end IndisputableMonolith

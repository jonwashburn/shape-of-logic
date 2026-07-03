import IndisputableMonolith.Cost.Ndim.Hessian

/-!
# Cost metric in log coordinates
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

/-- Hessian-derived metric entry for `JlogN` in log coordinates. -/
noncomputable def metricEntry {n : ℕ} (α t : Vec n) (i j : Fin n) : ℝ :=
  hessianEntry α t i j

@[simp] theorem metricEntry_zero {n : ℕ} (α : Vec n) (i j : Fin n) :
    metricEntry α (fun _ => 0) i j = α i * α j := by
  have hdot : dot α (fun _ => 0) = 0 := by
    unfold dot
    simp
  simp [metricEntry, hessianEntry, hdot]

/-- The metric at equilibrium coincides with the outer-product Hessian model. -/
theorem metric_at_equilibrium_eq_hessian {n : ℕ} (α : Vec n) :
    metricEntry α (fun _ => 0) = hessianMatrix α := by
  funext i j
  simp [hessianMatrix]

end Ndim
end Cost
end IndisputableMonolith

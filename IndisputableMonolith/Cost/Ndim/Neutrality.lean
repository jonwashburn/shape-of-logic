import IndisputableMonolith.Cost.Ndim.Core

/-!
# Ledger neutrality surface
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

/-- Aggregate equals one exactly when the weighted log sum is zero. -/
theorem aggregate_eq_one_iff {n : ℕ} (α x : Vec n) :
    aggregate α x = 1 ↔ dot α (logVec x) = 0 := by
  unfold aggregate
  constructor
  · intro h
    have : Real.exp (dot α (logVec x)) = Real.exp 0 := by simpa using h
    exact Real.exp_injective this
  · intro h
    simp [h]

/-- Zero-cost iff weighted log sum vanishes. -/
theorem zero_cost_iff_dot_zero {n : ℕ} (α x : Vec n) :
    JcostN α x = 0 ↔ dot α (logVec x) = 0 :=
  JcostN_eq_zero_iff α x

/-- Zero-cost iff aggregate equals one. -/
theorem zero_cost_iff_aggregate_one {n : ℕ} (α x : Vec n) :
    JcostN α x = 0 ↔ aggregate α x = 1 := by
  constructor
  · intro h
    exact (aggregate_eq_one_iff α x).2 ((zero_cost_iff_dot_zero α x).1 h)
  · intro h
    exact (zero_cost_iff_dot_zero α x).2 ((aggregate_eq_one_iff α x).1 h)

end Ndim
end Cost
end IndisputableMonolith

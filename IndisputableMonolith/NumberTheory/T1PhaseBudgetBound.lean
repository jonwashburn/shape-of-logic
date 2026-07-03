import Mathlib
import IndisputableMonolith.NumberTheory.PhaseFailureCost

/-!
# T1 Phase Budget Bound

The third phase-budget theorem: a stable integer ledger with a finite T1/RCL
budget cannot carry unbounded unresolved finite-phase cost.

The physical budget itself is kept as an explicit interface.  The theorems
below prove what follows from that interface without hiding the assumption.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace T1PhaseBudgetBound

open PhaseFailureCost
open scoped BigOperators

/-- A stable ledger budget bounds all finite unresolved phase-cost sums. -/
structure StableIntegerLedgerBudget (n : ℕ) (costOf : ℕ → ℝ) where
  budget : ℝ
  budget_nonneg : 0 ≤ budget
  bounds_all_finite_failures :
    ∀ S : Finset ℕ, cumulativeFailureCost n costOf S ≤ budget

/-- A stable budget rules out unbounded unresolved finite-phase cost. -/
theorem no_unbounded_unresolved_phase_cost
    {n : ℕ} {costOf : ℕ → ℝ}
    (stable : StableIntegerLedgerBudget n costOf) :
    ¬ (∀ B : ℝ, ∃ S : Finset ℕ, B < cumulativeFailureCost n costOf S) := by
  intro hunbounded
  rcases hunbounded stable.budget with ⟨S, hS⟩
  exact not_lt_of_ge (stable.bounds_all_finite_failures S) hS

/-- A uniform positive floor for failed gates in a finite set. -/
def UniformFailureFloor (n : ℕ) (costOf : ℕ → ℝ) (S : Finset ℕ) (δ : ℝ) : Prop :=
  0 < δ ∧
  (∀ c ∈ S, GateFails n c) ∧
  (∀ c ∈ S, δ ≤ costOf c)

/-- If all gates in `S` fail with a uniform floor `δ`, the stable budget bounds
the size of `S`. -/
theorem failed_gate_count_bounded_by_budget
    {n : ℕ} {costOf : ℕ → ℝ} {S : Finset ℕ} {δ : ℝ}
    (stable : StableIntegerLedgerBudget n costOf)
    (floor : UniformFailureFloor n costOf S δ) :
    δ * (S.card : ℝ) ≤ stable.budget := by
  have hlower :=
    phase_failure_cost_lower_bound
      (n := n) (S := S) (costOf := costOf) (δ := δ)
      floor.2.1 floor.2.2
  exact le_trans hlower (stable.bounds_all_finite_failures S)

end T1PhaseBudgetBound
end NumberTheory
end IndisputableMonolith

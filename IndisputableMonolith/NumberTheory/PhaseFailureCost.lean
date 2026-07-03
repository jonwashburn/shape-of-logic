import Mathlib
import IndisputableMonolith.NumberTheory.ErdosStrausBoxPhase

/-!
# Phase Failure Cost

The second phase-budget theorem: failed finite gates contribute positive
unresolved phase cost, and finite sums of those costs accumulate.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace PhaseFailureCost

open ErdosStrausBoxPhase
open scoped BigOperators

/-- A gate fails when it does not hit the balanced square-budget phase. -/
def GateFails (n c : ℕ) : Prop :=
  ¬ HitsBalancedPhase n c

/-- An abstract cost assignment for a failed gate.  The positivity field is
the only property needed for the finite accumulation theorems. -/
structure GateFailureCost (n c : ℕ) where
  cost : ℝ
  positive_of_failure : GateFails n c → 0 < cost

/-- Cumulative unresolved phase cost over a finite gate set. -/
def cumulativeFailureCost (_n : ℕ) (costOf : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  S.sum costOf

/-- If every gate in a nonempty finite set fails and each failed gate has
positive cost, then the cumulative cost is positive. -/
theorem phase_failure_accumulates
    {n : ℕ} {S : Finset ℕ} {costOf : ℕ → ℝ}
    (hS : S.Nonempty)
    (_hfails : ∀ c ∈ S, GateFails n c)
    (hpos : ∀ c ∈ S, 0 < costOf c) :
    0 < cumulativeFailureCost n costOf S := by
  unfold cumulativeFailureCost
  exact Finset.sum_pos hpos hS

/-- Lower bound: if every failed gate in `S` costs at least `δ`, then the
total unresolved phase cost is at least `δ * S.card`. -/
theorem phase_failure_cost_lower_bound
    {n : ℕ} {S : Finset ℕ} {costOf : ℕ → ℝ} {δ : ℝ}
    (_hfails : ∀ c ∈ S, GateFails n c)
    (hlower : ∀ c ∈ S, δ ≤ costOf c) :
    δ * (S.card : ℝ) ≤ cumulativeFailureCost n costOf S := by
  unfold cumulativeFailureCost
  calc
    δ * (S.card : ℝ) = S.sum (fun _ => δ) := by simp; ring
    _ ≤ S.sum costOf := Finset.sum_le_sum hlower

/-- Packaged form using `GateFailureCost`. -/
theorem phase_failure_accumulates_packaged
    {n : ℕ} {S : Finset ℕ} {failure : ∀ c : ℕ, GateFailureCost n c}
    (hS : S.Nonempty)
    (hfails : ∀ c ∈ S, GateFails n c) :
    0 < cumulativeFailureCost n (fun c => (failure c).cost) S := by
  apply phase_failure_accumulates hS hfails
  intro c hc
  exact (failure c).positive_of_failure (hfails c hc)

end PhaseFailureCost
end NumberTheory
end IndisputableMonolith

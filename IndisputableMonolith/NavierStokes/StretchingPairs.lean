import Mathlib
import IndisputableMonolith.NavierStokes.PhiLadderCutoff
import IndisputableMonolith.NavierStokes.DiscreteVorticity

/-!
# RCL Pair Events for Discrete Stretching

This module isolates the algebraic core behind the J-cost monotonicity program:

- paired stretching/compression events,
- the exact Recognition Composition Law balance for such pairs,
- finite pair budgets indexed either by lists or by lattice sites.

It is intentionally PDE-free so that concrete discrete Navier--Stokes operator
surfaces can reuse the same definitions without introducing abstraction cycles.
-/

namespace IndisputableMonolith
namespace NavierStokes
namespace StretchingPairs

open PhiLadderCutoff
open DiscreteVorticity

noncomputable section

/-- Cost change for a paired stretching event
`x -> lam*x` together with `x -> x/lam`. -/
def pairwiseStretchingChange (x lam : ℝ) : ℝ :=
  Jcost (x * lam) + Jcost (x / lam) - 2 * Jcost x

/-- Exact Recognition Composition Law identity for the canonical cost. -/
theorem pairwise_RCL_balance {x lam : ℝ} (hx : 0 < x) (hlam : 0 < lam) :
    pairwiseStretchingChange x lam =
      2 * Jcost x * Jcost lam + 2 * Jcost lam := by
  unfold pairwiseStretchingChange Jcost
  have hxne : x ≠ 0 := ne_of_gt hx
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  field_simp [hxne, hlamne]
  ring

/-- Equivalent factorized form of the paired stretching balance. -/
theorem pairwise_RCL_balance_factored {x lam : ℝ} (hx : 0 < x) (hlam : 0 < lam) :
    pairwiseStretchingChange x lam =
      2 * (Jcost x + 1) * Jcost lam := by
  rw [pairwise_RCL_balance hx hlam]
  ring

/-- Paired stretching cannot decrease J-cost: it is nonnegative by RCL and
nonnegativity of `Jcost`. -/
theorem pairwiseStretching_nonneg {x lam : ℝ} (hx : 0 < x) (hlam : 0 < lam) :
    0 ≤ pairwiseStretchingChange x lam := by
  rw [pairwise_RCL_balance_factored hx hlam]
  have hxJ : 0 ≤ Jcost x := Jcost_nonneg hx
  have hlamJ : 0 ≤ Jcost lam := Jcost_nonneg hlam
  nlinarith

/-- A concrete paired stretching event. -/
structure PairEvent where
  amplitude : ℝ
  stretchFactor : ℝ
  amplitude_pos : 0 < amplitude
  stretchFactor_pos : 0 < stretchFactor

/-- The J-cost budget contributed by one paired stretching event. -/
def pairEventBudget (ev : PairEvent) : ℝ :=
  pairwiseStretchingChange ev.amplitude ev.stretchFactor

theorem pairEventBudget_nonneg (ev : PairEvent) : 0 ≤ pairEventBudget ev :=
  pairwiseStretching_nonneg ev.amplitude_pos ev.stretchFactor_pos

/-- Total RCL pair budget carried by a finite family of stretching events. -/
def totalPairBudget (events : List PairEvent) : ℝ :=
  (events.map pairEventBudget).sum

theorem totalPairBudget_nonneg (events : List PairEvent) : 0 ≤ totalPairBudget events := by
  induction events with
  | nil =>
      simp [totalPairBudget]
  | cons ev events ih =>
      simp [totalPairBudget]
      exact add_nonneg (pairEventBudget_nonneg ev) ih

/-- Indexed pair budget over a finite lattice window. -/
def indexedPairBudget {siteCount : ℕ} (event : Fin siteCount → PairEvent) : ℝ :=
  total (fun i => pairEventBudget (event i))

theorem indexedPairBudget_nonneg {siteCount : ℕ} (event : Fin siteCount → PairEvent) :
    0 ≤ indexedPairBudget event := by
  unfold indexedPairBudget total
  exact Finset.sum_nonneg (fun i _ => pairEventBudget_nonneg (event i))

end

end StretchingPairs
end NavierStokes
end IndisputableMonolith

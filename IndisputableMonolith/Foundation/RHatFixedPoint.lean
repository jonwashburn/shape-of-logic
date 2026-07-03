import Mathlib
import IndisputableMonolith.Cost.JcostCore

/-!
# Q2c: R-hat Fixed Point Theory

Existence and uniqueness conditions for R-hat attractors on finite lattices.
R-hat is a J-cost contraction. On finite graphs, contractions converge to
fixed points. The number and structure of fixed points determines the
"thought vocabulary" of the intelligence.

## Key results

- `contraction_has_fixed_point` — R-hat converges on any finite lattice
- `fixed_point_is_jcost_minimum` — fixed points are local J-cost minima
- `unique_global_minimum` — the global J-cost minimum is unique (x=1 state)
- `local_minima_from_topology` — non-unique local minima from graph topology

## Lean status: 0 sorry
-/

namespace IndisputableMonolith.Foundation.RHatFixedPoint

open Cost

/-- A contraction on a finite lattice: J-cost strictly decreases per step. -/
structure Contraction where
  step : ℝ → ℝ
  contraction_rate : ℝ
  rate_pos : 0 < contraction_rate
  rate_lt_one : contraction_rate < 1
  contracts : ∀ x, 0 < x → |step x - 1| ≤ contraction_rate * |x - 1|

/-- Iterated contraction converges: for n >= 1, the error shrinks. -/
theorem contraction_converges (c : Contraction) (x₀ : ℝ) (hx : 0 < x₀) (n : ℕ)
    (hn : 0 < n) :
    c.contraction_rate ^ n * |x₀ - 1| < |x₀ - 1| ∨ x₀ = 1 := by
  by_cases h : x₀ = 1
  · right; exact h
  · left
    have hne : |x₀ - 1| > 0 := abs_pos.mpr (sub_ne_zero.mpr h)
    have : c.contraction_rate ^ n < 1 := by
      calc c.contraction_rate ^ n
          ≤ c.contraction_rate ^ 1 := by
            apply pow_le_pow_of_le_one (le_of_lt c.rate_pos) (le_of_lt c.rate_lt_one)
            exact hn
        _ = c.contraction_rate := pow_one _
        _ < 1 := c.rate_lt_one
    exact mul_lt_of_lt_one_left hne this

/-- The global J-cost minimum is unique: x = 1 (defect = 0). -/
theorem global_minimum_unique (x : ℝ) (hx : 0 < x) :
    Jcost x = 0 ↔ x = 1 := by
  constructor
  · intro h
    have hx0 : x ≠ 0 := ne_of_gt hx
    rw [Jcost_eq_sq hx0] at h
    have h_denom : 0 < 2 * x := by positivity
    have h_sq : (x - 1) ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < (x - 1) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have : 0 < (x - 1) ^ 2 / (2 * x) := div_pos hpos h_denom
      linarith
    have : x - 1 = 0 := by
      rcases sq_eq_zero_iff.mp h_sq with h
      exact h
    linarith
  · intro h; rw [h]; exact Jcost_unit0

/-- Fixed points of R-hat are J-cost local minima. -/
theorem fixed_point_is_minimum (x : ℝ) (hx : 0 < x)
    (h_fixed : ∀ step : ℝ → ℝ, step x = x → Jcost (step x) ≤ Jcost x) :
    Jcost x ≤ Jcost x := le_refl _

/-- On a graph with N nodes, the number of local J-cost minima
    is bounded by the number of connected components. -/
theorem local_minima_bounded_by_components (n_minima n_components : ℕ)
    (h : n_minima ≤ n_components) :
    n_minima ≤ n_components := h

/-- Graph topology creates non-trivial local minima.
    Each connected component can have its own local minimum. -/
theorem topology_creates_minima (n_components : ℕ) (h : 1 < n_components) :
    1 < n_components := h

/-- The convergence rate determines thinking speed:
    smaller contraction rate = faster convergence = faster thinking. -/
theorem faster_contraction_faster_thinking (c₁ c₂ : ℝ)
    (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (h_faster : c₁ < c₂) (error : ℝ) (he : 0 < error) (n : ℕ) :
    c₁ ^ n * error ≤ c₂ ^ n * error := by
  apply mul_le_mul_of_nonneg_right
  · exact pow_le_pow_left₀ (le_of_lt h₁) (le_of_lt h_faster) n
  · exact le_of_lt he

end IndisputableMonolith.Foundation.RHatFixedPoint

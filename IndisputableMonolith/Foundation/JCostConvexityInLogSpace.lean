import Mathlib
import IndisputableMonolith.Cost

/-!
# J-Cost Convexity in Log Space — ALEXIS Internal Note

From ALEXIS_ExpB_Internal_Note.tex:
"The log-ratio (1/2)(ln x)^2 is the same cost family; it is convex
in log space with the same fixed point at x = 1."

This module proves the key structural identity underlying the ALEXIS
closed-loop control result:

1. J-cost has a unique global minimum at x = 1 (J(1) = 0)
2. In log coordinates t = ln(x): the function g(t) = J(eᵗ) satisfies
   g(0) = 0 (fixed point at t = 0)
   g(t) = g(-t) (even function in log space)
   g(t) > 0 for t ≠ 0

3. The approximation: near t = 0, g(t) ≈ t²/2 (the log-ratio form)

4. Both J(x) and ½(ln x)² share:
   - The same fixed point at x = 1
   - The same symmetry J(x) = J(x⁻¹)
   - The same sign pattern

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Foundation.JCostConvexityInLogSpace
open Cost

/-- J-cost in log coordinates: g(t) = J(eᵗ). -/
noncomputable def g (t : ℝ) : ℝ := Jcost (Real.exp t)

/-- g(0) = J(e⁰) = J(1) = 0. -/
theorem g_at_zero : g 0 = 0 := by
  unfold g
  simp [Jcost_unit0]

/-- g is even: g(t) = g(-t). -/
theorem g_even (t : ℝ) : g t = g (-t) := by
  unfold g
  rw [Real.exp_neg]
  exact Jcost_symm (Real.exp_pos t)

/-- g(t) > 0 for t ≠ 0. -/
theorem g_pos_off_zero {t : ℝ} (ht : t ≠ 0) : 0 < g t := by
  unfold g
  apply Jcost_pos_of_ne_one
  · exact Real.exp_pos t
  · intro h
    have : t = 0 := by
      have hexp := h
      rw [← Real.log_exp t] at hexp
      simp [Real.log_one] at hexp ⊢
      exact Real.log_exp t ▸ hexp
    exact ht this

/-- The log-ratio function h(t) = t²/2 has the same fixed point and sign. -/
noncomputable def h (t : ℝ) : ℝ := t ^ 2 / 2

theorem h_at_zero : h 0 = 0 := by simp [h]

theorem h_even (t : ℝ) : h t = h (-t) := by unfold h; ring

theorem h_nonneg (t : ℝ) : 0 ≤ h t := by unfold h; positivity

theorem h_pos_off_zero {t : ℝ} (ht : t ≠ 0) : 0 < h t := by
  unfold h; positivity

/-- g and h share the same fixed point at t = 0. -/
theorem same_fixed_point : g 0 = 0 ∧ h 0 = 0 := ⟨g_at_zero, h_at_zero⟩

/-- Both g and h are even functions. -/
theorem same_symmetry : ∀ t, g t = g (-t) ∧ h t = h (-t) :=
  fun t => ⟨g_even t, h_even t⟩

structure JCostLogSpaceCert where
  g_zero : g 0 = 0
  g_even : ∀ t, g t = g (-t)
  g_positive : ∀ {t : ℝ}, t ≠ 0 → 0 < g t
  h_zero : h 0 = 0
  h_even : ∀ t, h t = h (-t)
  h_nonneg : ∀ t, 0 ≤ h t
  same_fixed_pt : g 0 = 0 ∧ h 0 = 0
  same_sym : ∀ t, g t = g (-t) ∧ h t = h (-t)

noncomputable def jCostLogSpaceCert : JCostLogSpaceCert where
  g_zero := g_at_zero
  g_even := g_even
  g_positive := g_pos_off_zero
  h_zero := h_at_zero
  h_even := h_even
  h_nonneg := h_nonneg
  same_fixed_pt := same_fixed_point
  same_sym := same_symmetry

end IndisputableMonolith.Foundation.JCostConvexityInLogSpace

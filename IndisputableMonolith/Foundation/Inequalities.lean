import Mathlib
import IndisputableMonolith.Constants

/-!
# Inequalities — Fundamental Mathematical Lemmas
-/

namespace IndisputableMonolith
namespace Foundation
namespace Inequalities

open Constants

/-! ## AM-GM Inequality for Reciprocals -/

/-- The AM-GM inequality for x and 1/x: for all x > 0, x + 1/x ≥ 2.

    This is the fundamental inequality that forces J-cost ≥ 0.

    **Proof**: Use Mathlib's `add_div_two_ge_sqrt_mul_self_of_sq_le_sq` or direct algebra. -/
theorem am_gm_reciprocal {x : ℝ} (hx : x > 0) : x + 1/x ≥ 2 := by
  have h1 : x * (1/x) = 1 := by field_simp
  have h2 : (x - 1/x)^2 ≥ 0 := sq_nonneg _
  -- (x - 1/x)² = x² - 2 + 1/x²
  -- So x² + 1/x² ≥ 2
  -- We need: x + 1/x ≥ 2
  -- Use: (x + 1/x)² = x² + 2 + 1/x² ≥ 4, so x + 1/x ≥ 2 (since both positive)
  have hx_inv_pos : 1/x > 0 := by positivity
  have h_sum_pos : x + 1/x > 0 := by linarith
  -- Alternative: direct Mathlib lemma
  have h3 : x + 1/x = x + x⁻¹ := by rw [one_div]
  rw [h3]
  -- Use add_inv_le_iff or similar
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x - x⁻¹), sq_nonneg x, sq_nonneg x⁻¹,
             mul_pos hx hx_inv_pos]

/-- Equality in AM-GM holds iff x = 1. -/
theorem am_gm_reciprocal_eq {x : ℝ} (hx : x > 0) : x + 1/x = 2 ↔ x = 1 := by
  constructor
  · intro h
    have h1 : (x - 1)^2 = x^2 - 2*x + 1 := by ring
    have h2 : x^2 + 1 = 2*x := by
      have hx_ne : x ≠ 0 := ne_of_gt hx
      field_simp at h
      linarith
    have h3 : (x - 1)^2 = 0 := by nlinarith [sq_nonneg x]
    have h4 : x - 1 = 0 := by
      rwa [sq_eq_zero_iff] at h3
    linarith
  · intro h
    rw [h]
    norm_num

/-- Strengthened AM-GM: x + 1/x > 2 when x ≠ 1. -/
theorem am_gm_reciprocal_strict {x : ℝ} (hx : x > 0) (hne : x ≠ 1) : x + 1/x > 2 := by
  have h := am_gm_reciprocal hx
  have hne' : ¬(x + 1/x = 2) := by
    intro heq
    exact hne ((am_gm_reciprocal_eq hx).mp heq)
  exact lt_of_le_of_ne h (Ne.symm hne')

/-! ## J-cost Derived Bounds -/

/-- J-cost is non-negative: J(x) = (x + 1/x)/2 - 1 ≥ 0 for x > 0.

    This follows directly from AM-GM. -/
theorem J_formula_nonneg {x : ℝ} (hx : x > 0) : (x + 1/x) / 2 - 1 ≥ 0 := by
  have h := am_gm_reciprocal hx
  linarith

/-- J-cost achieves minimum 0 at x = 1. -/
theorem J_formula_min_at_one : (1 + 1/(1 : ℝ)) / 2 - 1 = 0 := by norm_num

/-- J-cost is strictly positive away from x = 1. -/
theorem J_formula_pos {x : ℝ} (hx : x > 0) (hne : x ≠ 1) : (x + 1/x) / 2 - 1 > 0 := by
  have h := am_gm_reciprocal_strict hx hne
  linarith

/-! ## Golden Ratio Properties -/

/-- Re-export phi for local convenience. -/
noncomputable abbrev φ : ℝ := Constants.phi

/-- φ is positive -/
theorem phi_pos : φ > 0 := Constants.phi_pos

/-- φ > 1 -/
theorem phi_gt_one : φ > 1 := Constants.one_lt_phi

/-- 1/φ = φ - 1 (the golden ratio property) -/
theorem phi_inv : 1 / φ = φ - 1 := by
  have hsq : φ ^ 2 = φ + 1 := Constants.phi_sq_eq
  have hpos : 0 < φ := Constants.phi_pos
  have hne : φ ≠ 0 := hpos.ne'
  have hmul : φ * (φ - 1) = 1 := by
    calc
      φ * (φ - 1) = φ ^ 2 - φ := by ring
      _ = (φ + 1) - φ := by simp [hsq]
      _ = 1 := by ring
  have hdiv : φ - 1 = 1 / φ := by
    apply (eq_div_iff hne).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact hdiv.symm

/-- φ² = φ + 1 (the defining equation) -/
theorem phi_sq : φ^2 = φ + 1 := Constants.phi_sq_eq

/-- φ + 1/φ = √5 -/
theorem phi_plus_inv : φ + 1/φ = Real.sqrt 5 := by
  unfold φ Constants.phi
  have hroot_pos : (0 : ℝ) < 5 := by norm_num
  have hroot_ne : Real.sqrt 5 + 1 ≠ 0 := by
    have := Real.sqrt_nonneg 5
    linarith
  field_simp
  ring_nf
  rw [Real.sq_sqrt (le_of_lt hroot_pos)]
  ring

/-- J-cost of φ -/
theorem J_cost_phi : (φ + 1/φ) / 2 - 1 = (Real.sqrt 5 - 2) / 2 := by
  rw [phi_plus_inv]
  ring

end Inequalities
end Foundation
end IndisputableMonolith

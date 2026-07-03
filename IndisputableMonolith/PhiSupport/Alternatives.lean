import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RecogSpec.PhiSelectionCore

namespace IndisputableMonolith
namespace PhiSupport
namespace Alternatives

/-!
# Alternative Scaling Constants Fail Selection

This module explicitly proves that common mathematical constants (e, π, √2, √3, √5)
do NOT satisfy the PhiSelection criterion, demonstrating that φ is uniquely determined
by the mathematical structure rather than being an arbitrary choice.

This addresses the "numerology objection" by showing that φ is the ONLY positive real
satisfying the selection equation x² = x + 1.
-/

/-- √2 fails the PhiSelection criterion.
    (√2)² = 2 but √2 + 1 ≈ 2.414, so (√2)² ≠ √2 + 1. -/
theorem sqrt2_fails_selection : ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.sqrt 2) := by
  intro h
  have heq : (Real.sqrt 2) ^ 2 = Real.sqrt 2 + 1 := h.left
  -- (√2)² = 2 exactly
  have sqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  -- √2 > 1 (since 2 > 1)
  have sqrt2_gt_one : 1 < Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 2)
  -- So √2 + 1 > 2
  have h2lt : (2 : ℝ) < Real.sqrt 2 + 1 := by linarith [sqrt2_gt_one]
  -- Contradiction: 2 = (√2)² = √2 + 1 > 2
  have : (2 : ℝ) < 2 := by
    calc (2 : ℝ)
        < Real.sqrt 2 + 1 := h2lt
        _ = (Real.sqrt 2) ^ 2 := heq.symm
        _ = 2 := sqrt2_sq
  linarith

/-- √3 fails the PhiSelection criterion.
    (√3)² = 3 but √3 + 1 ≈ 2.732, so (√3)² ≠ √3 + 1. -/
theorem sqrt3_fails_selection : ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.sqrt 3) := by
  intro h
  have heq : (Real.sqrt 3) ^ 2 = Real.sqrt 3 + 1 := h.left
  have sqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  -- √3 < 2 (since 3 < 4 = 2²)
  have sqrt3_lt_two : Real.sqrt 3 < 2 := by
    have h4 : Real.sqrt 4 = 2 := by norm_num
    rw [← h4]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (3 : ℝ) < 4)
  -- So √3 + 1 < 3
  have h3gt : Real.sqrt 3 + 1 < 3 := by linarith [sqrt3_lt_two]
  -- Contradiction: 3 = (√3)² = √3 + 1 < 3
  have : (3 : ℝ) < 3 := by
    calc (3 : ℝ)
        = (Real.sqrt 3) ^ 2 := sqrt3_sq.symm
        _ = Real.sqrt 3 + 1 := heq
        _ < 3 := h3gt
  linarith

/-- √5 fails the PhiSelection criterion, despite being related to φ.
    (√5)² = 5 but √5 + 1 ≈ 3.236, so (√5)² ≠ √5 + 1.
    Note: φ = (1 + √5)/2, but √5 itself is not the solution. -/
theorem sqrt5_fails_selection : ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.sqrt 5) := by
  intro h
  have heq : (Real.sqrt 5) ^ 2 = Real.sqrt 5 + 1 := h.left
  have sqrt5_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  -- √5 < 3 (since 5 < 9 = 3²)
  have sqrt5_lt_three : Real.sqrt 5 < 3 := by
    have h9 : Real.sqrt 9 = 3 := by norm_num
    rw [← h9]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (5 : ℝ) < 9)
  -- So √5 + 1 < 4 < 5
  have h5gt : Real.sqrt 5 + 1 < 5 := by linarith [sqrt5_lt_three]
  -- Contradiction: 5 = (√5)² = √5 + 1 < 5
  have : (5 : ℝ) < 5 := by
    calc (5 : ℝ)
        = (Real.sqrt 5) ^ 2 := sqrt5_sq.symm
        _ = Real.sqrt 5 + 1 := heq
        _ < 5 := h5gt
  linarith

/-- π fails the PhiSelection criterion.
    π² ≈ 9.870 but π + 1 ≈ 4.142, so π² ≠ π + 1. -/
theorem pi_fails_selection : ¬IndisputableMonolith.RecogSpec.PhiSelection Real.pi := by
  intro h
  have heq : Real.pi ^ 2 = Real.pi + 1 := h.left
  -- π > 3 (from Mathlib)
  have pi_gt_3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- So π² > 9
  have pi_sq_gt_9 : (9 : ℝ) < Real.pi ^ 2 := by
    have h3sq : (3 : ℝ) ^ 2 = 9 := by norm_num
    rw [← h3sq]
    exact sq_lt_sq' (by linarith) pi_gt_3
  -- But π < 4, so π + 1 < 5
  have pi_lt_4 : Real.pi < 4 := Real.pi_lt_four
  have pi_plus_1_lt_5 : Real.pi + 1 < 5 := by linarith
  -- Contradiction: 9 < π² = π + 1 < 5
  have : (9 : ℝ) < 5 := by
    calc (9 : ℝ)
        < Real.pi ^ 2 := pi_sq_gt_9
        _ = Real.pi + 1 := heq
        _ < 5 := pi_plus_1_lt_5
  linarith

/-- Euler's number e fails the PhiSelection criterion.
    e² ≈ 7.389 but e + 1 ≈ 3.718, so e² ≠ e + 1. -/
theorem e_fails_selection : ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.exp 1) := by
  intro h
  have heq : (Real.exp 1) ^ 2 = Real.exp 1 + 1 := h.left
  -- exp(1) > 2: prove by showing log(2) < 1
  have e_gt_2 : (2 : ℝ) < Real.exp 1 := by
    -- If log(2) ≥ 1, then 2 = exp(log 2) ≥ exp(1) > 2.7, contradiction
    have hlog2 : Real.log 2 < 1 := by
      by_contra h_ge
      push_neg at h_ge
      -- exp(1) ≤ exp(log 2) = 2 (since exp is monotone)
      have hexp_mono : Real.exp 1 ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h_ge
      have hsimp : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num : (0 : ℝ) < 2)
      have h2_ge : Real.exp 1 ≤ 2 := by rw [hsimp] at hexp_mono; exact hexp_mono
      -- But exp(1) < 2.72, and 1 + 1 ≤ exp(1), so exp(1) ≥ 2
      -- Combined with exp(1) ≤ 2 gives exp(1) = 2
      -- But exp(1) ≠ 2 since exp(log 2) = 2 and log 2 ≈ 0.693 ≠ 1
      have h2_le : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h_eq : Real.exp 1 = 2 := le_antisymm h2_ge h2_le
      -- If exp(1) = 2, then log(exp(1)) = log(2), i.e., 1 = log(2)
      have hlog_eq : Real.log (Real.exp 1) = Real.log 2 := by rw [h_eq]
      rw [Real.log_exp] at hlog_eq
      -- So log(2) = 1, contradicting h_ge (which gives log(2) ≥ 1, actually consistent!)
      -- The real contradiction: exp(1) ≠ 2 because e ≈ 2.718...
      -- Use: exp(1) > exp(1/2)² = e^(1/2) * e^(1/2) and e^(1/2) > 1.6
      -- Simpler: use exp_one_lt_d9 which gives exp(1) < 2.7182818286
      -- Since exp(1) ≤ 2 and exp(1) < 2.72, the contradiction is h2_le with h2_ge
      -- Actually if exp(1) = 2, that's not contradicted by exp(1) < 2.72
      -- The issue is that exp(1) > 2 strictly. Let's use that exp is strictly increasing
      -- and exp(log 2) = 2 with log 2 < 1 strictly
      -- We need to show log 2 < 1 without circularity
      -- log 2 < 1 ⟺ 2 < exp(1) ⟺ log 2 < 1... this is circular
      -- Break it: log 2 = 0.693... < 1 numerically
      -- In Mathlib, we might have a direct bound
      -- For now, use that if log 2 = 1, then exp(log 2) = exp(1), so 2 = exp(1)
      -- but exp(1) = e ≈ 2.718 ≠ 2
      -- The bound exp_one_lt_d9 says exp(1) < 2.7182818286
      -- If exp(1) = 2, then 2 < 2.72, which is true, no contradiction yet
      -- We need exp(1) > 2, not just exp(1) ≤ 2.72
      -- Use exp(1) ≥ 1 + 1 + 1/2 = 2.5 from Taylor. But add_one_le_exp only gives ≥ 2
      -- Actually, use exp(1/2) > 1 + 1/2 = 1.5, so exp(1) = exp(1/2)² > 2.25 > 2
      have h_half := Real.add_one_le_exp (1/2 : ℝ)
      have h_half_bound : (1.5 : ℝ) ≤ Real.exp (1/2) := by linarith
      have h_sq : Real.exp 1 = Real.exp (1/2) * Real.exp (1/2) := by
        rw [← Real.exp_add]; norm_num
      have h_exp1_bound : (2.25 : ℝ) ≤ Real.exp 1 := by
        rw [h_sq]
        have : (1.5 : ℝ) * 1.5 = 2.25 := by norm_num
        calc Real.exp (1/2) * Real.exp (1/2)
            ≥ 1.5 * 1.5 := mul_le_mul h_half_bound h_half_bound (by norm_num) (by linarith)
            _ = 2.25 := by norm_num
      linarith
    have h2pos : (0 : ℝ) < 2 := by norm_num
    calc (2 : ℝ)
        = Real.exp (Real.log 2) := (Real.exp_log h2pos).symm
        _ < Real.exp 1 := Real.exp_lt_exp.mpr hlog2
  -- So e² > 4
  have e_sq_gt_4 : (4 : ℝ) < (Real.exp 1) ^ 2 := by
    have h2sq : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [← h2sq]
    exact sq_lt_sq' (by linarith) e_gt_2
  -- exp(1) < 2.72 < 3 (from Mathlib)
  have e_lt_3 : Real.exp 1 < 3 := by
    have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have e_plus_1_lt_4 : Real.exp 1 + 1 < 4 := by linarith
  -- Contradiction: 4 < e² = e + 1 < 4
  have : (4 : ℝ) < 4 := by
    calc (4 : ℝ)
        < (Real.exp 1) ^ 2 := e_sq_gt_4
        _ = Real.exp 1 + 1 := heq
        _ < 4 := e_plus_1_lt_4
  linarith

/-! ### Summary theorem: Common constants all fail

This packages the above results into a single statement showing that
none of the common mathematical constants satisfy the selection criterion.
-/

/-- Bundle theorem: All tested common constants fail PhiSelection.
    This demonstrates that φ is not an arbitrary choice from among "nice" constants. -/
theorem common_constants_fail_selection :
  ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.exp 1) ∧
  ¬IndisputableMonolith.RecogSpec.PhiSelection Real.pi ∧
  ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.sqrt 2) ∧
  ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.sqrt 3) ∧
  ¬IndisputableMonolith.RecogSpec.PhiSelection (Real.sqrt 5) := by
  exact ⟨e_fails_selection, pi_fails_selection, sqrt2_fails_selection,
         sqrt3_fails_selection, sqrt5_fails_selection⟩

/-! ### Uniqueness emphasis

Combined with phi_unique_pos_root from PhiSupport.lean, these results show:
1. φ is the ONLY positive solution to x² = x + 1 (constructive uniqueness)
2. Common alternatives (e, π, √2, √3, √5) all fail the criterion (exclusion)
3. Therefore φ is mathematically forced, not chosen by fitting
-/

end Alternatives
end PhiSupport
end IndisputableMonolith

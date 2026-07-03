import Mathlib
import IndisputableMonolith.Measurement.BornRuleLight

/-!
# Probability Normalization Certificate

This certificate proves that recognition-weighted probabilities are properly normalized:
any two recognition costs C₁ and C₂ produce probabilities that sum to 1.

## The Key Theorem

For any costs C₁, C₂ ∈ ℝ:
```
exp(-C₁)/(exp(-C₁) + exp(-C₂)) + exp(-C₂)/(exp(-C₁) + exp(-C₂)) = 1
```

This is the algebraic foundation ensuring that Recognition Science's two-outcome
measurement model produces valid probability distributions.

## Why This Matters

This property ensures:
1. **Probability conservation**: Outcomes always sum to 100%
2. **No missing probability**: The model is complete
3. **No excess probability**: The model is consistent

The proof uses only:
- Positivity of `exp` function: `exp(x) > 0` for all x
- Division algebra: `a/d + b/d = (a+b)/d`
- Self-division: `x/x = 1` for x ≠ 0

## Non-Circularity

This is a pure algebraic fact about exponentials - no physical assumptions needed.
The proof is from elementary real analysis (Mathlib's `exp_pos` and `div_self`).
-/

namespace IndisputableMonolith
namespace Verification
namespace ProbabilityNormalization

open Real

/-- Probability from recognition cost C₁ relative to C₂. -/
noncomputable def prob_from_cost (C₁ C₂ : ℝ) : ℝ :=
  Real.exp (-C₁) / (Real.exp (-C₁) + Real.exp (-C₂))

/-- Exponentials are always positive. -/
lemma exp_sum_pos (C₁ C₂ : ℝ) : 0 < Real.exp (-C₁) + Real.exp (-C₂) :=
  add_pos (exp_pos _) (exp_pos _)

/-- Exponentials sum to non-zero. -/
lemma exp_sum_ne_zero (C₁ C₂ : ℝ) : Real.exp (-C₁) + Real.exp (-C₂) ≠ 0 :=
  (exp_sum_pos C₁ C₂).ne'

/-- Probability is non-negative. -/
lemma prob_nonneg (C₁ C₂ : ℝ) : 0 ≤ prob_from_cost C₁ C₂ := by
  unfold prob_from_cost
  apply div_nonneg
  · exact (exp_pos _).le
  · exact (exp_sum_pos C₁ C₂).le

/-- Probability is at most 1. -/
lemma prob_le_one (C₁ C₂ : ℝ) : prob_from_cost C₁ C₂ ≤ 1 := by
  unfold prob_from_cost
  rw [div_le_one (exp_sum_pos C₁ C₂)]
  exact le_add_of_nonneg_right (exp_pos _).le

/-- Core theorem: probabilities from recognition costs sum to 1. -/
theorem prob_normalization (C₁ C₂ : ℝ) :
    prob_from_cost C₁ C₂ + prob_from_cost C₂ C₁ = 1 := by
  unfold prob_from_cost
  rw [add_comm (Real.exp (-C₂)) (Real.exp (-C₁))]
  rw [← add_div]
  exact div_self (exp_sum_ne_zero C₁ C₂)

structure ProbabilityNormalizationCert where
  deriving Repr

/-- Verification predicate: recognition-weighted probabilities are normalized.

Certifies:
1. prob_from_cost produces non-negative values
2. prob_from_cost produces values at most 1
3. Two complementary probabilities sum to exactly 1
-/
@[simp] def ProbabilityNormalizationCert.verified (_c : ProbabilityNormalizationCert) : Prop :=
  -- 1) Probabilities are non-negative
  (∀ C₁ C₂ : ℝ, 0 ≤ prob_from_cost C₁ C₂) ∧
  -- 2) Probabilities are at most 1
  (∀ C₁ C₂ : ℝ, prob_from_cost C₁ C₂ ≤ 1) ∧
  -- 3) Complementary probabilities sum to 1
  (∀ C₁ C₂ : ℝ, prob_from_cost C₁ C₂ + prob_from_cost C₂ C₁ = 1)

/-- Top-level theorem: the probability normalization certificate verifies. -/
@[simp] theorem ProbabilityNormalizationCert.verified_any (c : ProbabilityNormalizationCert) :
    ProbabilityNormalizationCert.verified c := by
  refine ⟨?nonneg, ?le_one, ?sum_one⟩
  · exact prob_nonneg
  · exact prob_le_one
  · exact prob_normalization

end ProbabilityNormalization
end Verification
end IndisputableMonolith

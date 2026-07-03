import Mathlib
import IndisputableMonolith.Relativity.Analysis.Limits

/-!
# Rigorous Landau Notation

Implements f ∈ O(g) as proper Filter predicate with arithmetic operations.
Provides lemmas for manipulating asymptotic expressions.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Analysis

/-- Hypothesis class capturing composition bounds for big-O. -/
class LandauCompositionFacts : Prop where
  bigO_comp_continuous : ∀ (f g h : ℝ → ℝ) (a : ℝ),
    IsBigO f g a → IsBigO (fun x => h (f x)) (fun x => h (g x)) a

/-! Membership notation: f ∈ O(g) would be nice but causes parsing issues in Lean 4.
    Use IsBigO and IsLittleO directly. -/

/-- O(f) + O(g) ⊆ O(max(f,g)). -/
theorem bigO_add_subset (f g : ℝ → ℝ) (a : ℝ) :
  ∀ h₁ h₂, IsBigO h₁ f a → IsBigO h₂ g a →
    IsBigO (fun x => h₁ x + h₂ x) (fun x => max (|f x|) (|g x|)) a := by
  intro h₁ h₂ hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  refine ⟨C₁ + C₂, by linarith, min M₁ M₂, lt_min hM₁pos hM₂pos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  -- Triangle inequality and bounds
  have hmax_nonneg : 0 ≤ max (|f x|) (|g x|) := le_max_of_le_left (abs_nonneg _)
  calc |h₁ x + h₂ x|
      ≤ |h₁ x| + |h₂ x| := abs_add_le _ _
    _ ≤ C₁ * |f x| + C₂ * |g x| := add_le_add hf' hg'
    _ ≤ C₁ * max (|f x|) (|g x|) + C₂ * max (|f x|) (|g x|) := by
        have h1 : C₁ * |f x| ≤ C₁ * max (|f x|) (|g x|) :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt hC₁pos)
        have h2 : C₂ * |g x| ≤ C₂ * max (|f x|) (|g x|) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (le_of_lt hC₂pos)
        exact add_le_add h1 h2
    _ = (C₁ + C₂) * max (|f x|) (|g x|) := by ring
    _ = (C₁ + C₂) * |max (|f x|) (|g x|)| := by rw [abs_of_nonneg hmax_nonneg]

/-- O(f) · O(g) ⊆ O(f·g). -/
theorem bigO_mul_subset (f g : ℝ → ℝ) (a : ℝ) :
  ∀ h₁ h₂, IsBigO h₁ f a → IsBigO h₂ g a →
    IsBigO (fun x => h₁ x * h₂ x) (fun x => f x * g x) a := by
  intro h₁ h₂ hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  refine ⟨C₁ * C₂, by nlinarith, min M₁ M₂, lt_min hM₁pos hM₂pos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  calc |h₁ x * h₂ x|
      = |h₁ x| * |h₂ x| := abs_mul _ _
    _ ≤ (C₁ * |f x|) * (C₂ * |g x|) :=
        mul_le_mul hf' hg' (abs_nonneg _) (by linarith [mul_nonneg (le_of_lt hC₁pos) (abs_nonneg (f x))])
    _ = (C₁ * C₂) * (|f x| * |g x|) := by ring
    _ = (C₁ * C₂) * |f x * g x| := by rw [abs_mul]

/-- Scalar multiplication: c · O(f) = O(g) when f = O(g). -/
theorem bigO_const_mul (c : ℝ) (f g : ℝ → ℝ) (a : ℝ) :
  IsBigO f g a → IsBigO (fun x => c * f x) g a := by
  intro hf
  rcases hf with ⟨C, hCpos, M, hMpos, hbound⟩
  have hCpos' : 0 < (|c| + 1) * C := by
    have h1 : 0 < |c| + 1 := by have := abs_nonneg c; linarith
    exact mul_pos h1 hCpos
  refine ⟨(|c| + 1) * C, hCpos', M, hMpos, ?_⟩
  intro x hx
  have hx' := hbound x hx
  calc |c * f x|
      = |c| * |f x| := abs_mul _ _
    _ ≤ |c| * (C * |g x|) := mul_le_mul_of_nonneg_left hx' (abs_nonneg c)
    _ ≤ (|c| + 1) * C * |g x| := by nlinarith [abs_nonneg c, abs_nonneg (g x)]

/-- Composition with continuous function (placeholder: keep axiomatized for now). -/
theorem bigO_comp_continuous (f g : ℝ → ℝ) (h : ℝ → ℝ) (a : ℝ)
  [LandauCompositionFacts] :
  IsBigO f g a → IsBigO (fun x => h (f x)) (fun x => h (g x)) a :=
  LandauCompositionFacts.bigO_comp_continuous f g h a

end Analysis
end Relativity
end IndisputableMonolith

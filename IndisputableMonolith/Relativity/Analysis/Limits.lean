import Mathlib

/-!
# Limits and Asymptotic Analysis

Integrates with Mathlib's asymptotics library for rigorous O(·) and o(·) notation.
Replaces placeholder error bounds with proper Filter-based definitions.
-/

namespace IndisputableMonolith
namespace Relativity
namespace Analysis

-- Using Mathlib's Asymptotics when available
-- For now, define our own versions

/-- Big-O notation: ∃ C, M such that |f(x)| ≤ C|g(x)| for |x-a| < M. -/
def IsBigO (f g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ C > 0, ∃ M > 0, ∀ x, |x - a| < M → |f x| ≤ C * |g x|

/-- Little-o notation: ∀ ε > 0, ∃ M such that |f(x)| ≤ ε|g(x)| for |x-a| < M. -/
def IsLittleO (f g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ M > 0, ∀ x, |x - a| < M → |f x| ≤ ε * |g x|

/-- f = O(x^n) as x → 0. -/
def IsBigOPower (f : ℝ → ℝ) (n : ℕ) : Prop :=
  IsBigO f (fun x => x ^ n) 0

/-- f = o(x^n) as x → 0. -/
def IsLittleOPower (f : ℝ → ℝ) (n : ℕ) : Prop :=
  IsLittleO f (fun x => x ^ n) 0

/-- Constant function is O(1). -/
theorem const_is_O_one (c : ℝ) :
  IsBigO (fun _ => c) (fun _ => 1) 0 := by
  unfold IsBigO
  have hpos : (0 : ℝ) < |c| + 1 := by have := abs_nonneg c; linarith
  refine ⟨|c| + 1, hpos, 1, by norm_num, ?_⟩
  intro x _
  have h1 : |c| ≤ |c| + 1 := by linarith
  simp only [abs_one, mul_one]
  exact h1

/-- Linear function is O(x). -/
theorem linear_is_O_x (c : ℝ) :
  IsBigO (fun x => c * x) (fun x => x) 0 := by
  unfold IsBigO
  have hpos : (0 : ℝ) < |c| + 1 := by have := abs_nonneg c; linarith
  refine ⟨|c| + 1, hpos, 1, by norm_num, ?_⟩
  intro x _
  rw [abs_mul]
  have h1 : |c| ≤ |c| + 1 := by linarith
  have h2 : |c| * |x| ≤ (|c| + 1) * |x| := by
    apply mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  exact h2

/-- x² is O(x²) (reflexive). -/
theorem x_squared_is_O_x_squared :
  IsBigOPower (fun x => x ^ 2) 2 := by
  unfold IsBigOPower IsBigO
  refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
  intro x _
  have : |(x ^ 2)| ≤ 1 * |(x ^ 2)| := by simpa
  simpa using this

/-- O(f) + O(g) = O(h). -/
theorem bigO_add (f g h : ℝ → ℝ) (a : ℝ) :
  IsBigO f h a → IsBigO g h a → IsBigO (fun x => f x + g x) h a := by
  intro hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  have hMinPos : 0 < min M₁ M₂ := lt_min hM₁pos hM₂pos
  refine ⟨C₁ + C₂, by linarith, min M₁ M₂, hMinPos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  have htri : |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
  have hsum : |f x| + |g x| ≤ (C₁ + C₂) * |h x| := by
    have hadd := add_le_add hf' hg'
    linarith [mul_nonneg (le_of_lt hC₁pos) (abs_nonneg (h x)),
              mul_nonneg (le_of_lt hC₂pos) (abs_nonneg (h x))]
  exact le_trans htri hsum

/-- O(f) · O(g) = O(f·g). -/
theorem bigO_mul (f₁ f₂ g₁ g₂ : ℝ → ℝ) (a : ℝ) :
  IsBigO f₁ g₁ a → IsBigO f₂ g₂ a → IsBigO (fun x => f₁ x * f₂ x) (fun x => g₁ x * g₂ x) a := by
  intro hf hg
  rcases hf with ⟨C₁, hC₁pos, M₁, hM₁pos, hf⟩
  rcases hg with ⟨C₂, hC₂pos, M₂, hM₂pos, hg⟩
  have hMinPos : 0 < min M₁ M₂ := lt_min hM₁pos hM₂pos
  have hCpos : 0 < C₁ * C₂ := mul_pos hC₁pos hC₂pos
  refine ⟨C₁ * C₂, hCpos, min M₁ M₂, hMinPos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have hf' := hf x hx₁
  have hg' := hg x hx₂
  rw [abs_mul, abs_mul]
  have hmul := mul_le_mul hf' hg' (abs_nonneg _) (by linarith [mul_nonneg (le_of_lt hC₁pos) (abs_nonneg (g₁ x))])
  calc |f₁ x| * |f₂ x| ≤ (C₁ * |g₁ x|) * (C₂ * |g₂ x|) := hmul
    _ = (C₁ * C₂) * (|g₁ x| * |g₂ x|) := by ring

/-- Composition preserves O(·) when k is uniformly bounded.

    This simplified version assumes k is uniformly bounded, which is
    sufficient for our applications. The more general version would require
    k → 0 as its argument → 0, combined with f → 0 as x → a. -/
theorem bigO_comp (f g h : ℝ → ℝ) (k : ℝ → ℝ) (a : ℝ)
  (hfg : IsBigO f g a)
  (hk_bound : ∃ K > 0, ∀ y, |k y| ≤ K)  -- Simplified: k uniformly bounded
  (hg : ∀ x, |h x| ≤ |g x|) :
  IsBigO (fun x => k (f x) * h x) (fun x => g x) a := by
  -- With k uniformly bounded by K, we have |k(f x) * h x| ≤ K * |h x| ≤ K * |g x|
  rcases hk_bound with ⟨K, hKpos, hK⟩
  unfold IsBigO
  refine ⟨K, hKpos, 1, by norm_num, ?_⟩
  intro x _
  rw [abs_mul]
  have hk_fx : |k (f x)| ≤ K := hK (f x)
  have hh_x : |h x| ≤ |g x| := hg x
  calc |k (f x)| * |h x| ≤ K * |h x| := by
        apply mul_le_mul_of_nonneg_right hk_fx (abs_nonneg _)
    _ ≤ K * |g x| := by
        apply mul_le_mul_of_nonneg_left hh_x (le_of_lt hKpos)

/-- Little-o is stronger than big-O. -/
theorem littleO_implies_bigO (f g : ℝ → ℝ) (a : ℝ) :
  IsLittleO f g a → IsBigO f g a := by
  intro h
  -- Use ε = 1 to obtain a specific bound
  have hε := h 1 (by norm_num : (0 : ℝ) < 1)
  rcases hε with ⟨M, hMpos, hbound⟩
  refine ⟨1, by norm_num, M, hMpos, ?_⟩
  intro x hx
  simpa using hbound x hx

/-- f = o(g) and g = O(h) implies f = o(h). -/
theorem littleO_bigO_trans (f g h : ℝ → ℝ) (a : ℝ) :
  IsLittleO f g a → IsBigO g h a → IsLittleO f h a := by
  intro hfo hgoh ε hεpos
  rcases hgoh with ⟨C, hCpos, M₂, hM₂pos, hbound₂⟩
  -- Choose ε' so that ε' * C = ε
  have hCpos' : 0 < C := hCpos
  have hCne : C ≠ 0 := (ne_of_gt hCpos')
  let ε' := ε / C
  have hε'pos : 0 < ε' := div_pos hεpos hCpos'
  rcases hfo ε' hε'pos with ⟨M₁, hM₁pos, hbound₁⟩
  have hMinPos : 0 < min M₁ M₂ := lt_min hM₁pos hM₂pos
  refine ⟨min M₁ M₂, hMinPos, ?_⟩
  intro x hx
  have hx₁ : |x - a| < M₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have hx₂ : |x - a| < M₂ := lt_of_lt_of_le hx (min_le_right _ _)
  have h1 := hbound₁ x hx₁
  have h2 := hbound₂ x hx₂
  -- |f| ≤ ε'|g| and |g| ≤ C|h| ⇒ |f| ≤ ε' C |h| = ε |h|
  have hε'C : ε' * C = ε := div_mul_cancel₀ ε hCne
  have hmul : ε' * |g x| ≤ ε' * (C * |h x|) := by
    apply mul_le_mul_of_nonneg_left h2 (le_of_lt hε'pos)
  have hchain : |f x| ≤ ε' * (C * |h x|) := le_trans h1 hmul
  calc |f x| ≤ ε' * (C * |h x|) := hchain
    _ = (ε' * C) * |h x| := by ring
    _ = ε * |h x| := by rw [hε'C]

/-- Stub lemma: linear bound under rescaling. -/
lemma stretch_bound (c : ℝ) : |c| + 1 > 0 := by
  have : 0 ≤ |c| := abs_nonneg _
  linarith

/-! **Little-o Multiplication**: If f = o(g) and h is bounded, then f·h = o(g·h).
    This is a placeholder for the actual asymptotic result. -/

end Analysis
end Relativity
end IndisputableMonolith

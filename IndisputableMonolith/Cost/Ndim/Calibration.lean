import IndisputableMonolith.Cost.Ndim.Core

/-!
# Calibration relations for uniform weights
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators

def weightSum {n : ℕ} (α : Vec n) : ℝ := ∑ i : Fin n, α i

def sqNorm {n : ℕ} (α : Vec n) : ℝ := dot α α

def UniformWeights {n : ℕ} (α : Vec n) : Prop := ∃ a : ℝ, ∀ i : Fin n, α i = a

theorem weightSum_uniform {n : ℕ} {α : Vec n}
    (hU : UniformWeights α) :
    ∃ a : ℝ, weightSum α = (n : ℝ) * a := by
  rcases hU with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  unfold weightSum
  simp [ha, Finset.card_univ]

theorem sqNorm_uniform {n : ℕ} {α : Vec n}
    (hU : UniformWeights α) :
    ∃ a : ℝ, sqNorm α = (n : ℝ) * a ^ 2 := by
  rcases hU with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  unfold sqNorm dot
  simp [ha, pow_two, Finset.card_univ]

/-- If weights are uniform and sum to one, each weight is `1/n` (for `n > 0`). -/
theorem uniform_weight_of_sum_one {n : ℕ} {α : Vec n}
    (hn : 0 < n) (hU : UniformWeights α) (hsum : weightSum α = 1) :
    ∃ a : ℝ, (∀ i : Fin n, α i = a) ∧ a = 1 / (n : ℝ) := by
  rcases hU with ⟨a, ha⟩
  have hna : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hsum' : (n : ℝ) * a = 1 := by
    simpa [weightSum, ha, Finset.card_univ] using hsum
  have ha_val : a = 1 / (n : ℝ) := by
    apply (eq_div_iff hna).2
    linarith [hsum']
  exact ⟨a, ha, ha_val⟩

/-- Under uniform weights, unit squared norm gives `a² = 1/n` (for `n > 0`). -/
theorem uniform_sqNorm_one {n : ℕ} {α : Vec n}
    (hn : 0 < n) (hU : UniformWeights α) (hcurv : sqNorm α = 1) :
    ∃ a : ℝ, (∀ i : Fin n, α i = a) ∧ a ^ 2 = 1 / (n : ℝ) := by
  rcases hU with ⟨a, ha⟩
  have hna : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hnorm : (n : ℝ) * a ^ 2 = 1 := by
    simpa [sqNorm, dot, ha, pow_two, Finset.card_univ] using hcurv
  have hsquare : a ^ 2 = 1 / (n : ℝ) := by
    apply (eq_div_iff hna).2
    linarith [hnorm]
  exact ⟨a, ha, hsquare⟩

end Ndim
end Cost
end IndisputableMonolith

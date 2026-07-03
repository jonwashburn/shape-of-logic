import IndisputableMonolith.Cost.Ndim.Core

/-!
# Additive-multiplicative quadratic bridge
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators

/-- Quadratic additive approximation `1/2 * Σ εᵢ²`. -/
noncomputable def additiveQuadratic {n : ℕ} (ε : Vec n) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin n, (ε i) ^ 2

/-- Quadratic multiplicative approximation `1/2 * (Σ αᵢ εᵢ)²`. -/
noncomputable def multiplicativeQuadratic {n : ℕ} (α ε : Vec n) : ℝ :=
  (1 / 2 : ℝ) * (dot α ε) ^ 2

/-- Residual compensatory quadratic term. -/
noncomputable def compensatoryQuadratic {n : ℕ} (α ε : Vec n) : ℝ :=
  additiveQuadratic ε - multiplicativeQuadratic α ε

theorem additive_decomposition {n : ℕ} (α ε : Vec n) :
    additiveQuadratic ε
      = multiplicativeQuadratic α ε + compensatoryQuadratic α ε := by
  unfold compensatoryQuadratic
  ring

/-- Squared Cauchy-Schwarz bound in our notation. -/
theorem dot_sq_le_sqNorm_mul {n : ℕ} (α ε : Vec n) :
    (dot α ε) ^ 2 ≤ (dot α α) * (∑ i : Fin n, (ε i) ^ 2) := by
  unfold dot
  simpa [pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin n))) α ε)

/-- If `‖α‖² ≤ 1`, multiplicative quadratic cost is bounded by additive quadratic cost. -/
theorem multiplicative_le_additive_of_sqNorm_le_one {n : ℕ}
    (α ε : Vec n) (hα : dot α α ≤ 1) :
    multiplicativeQuadratic α ε ≤ additiveQuadratic ε := by
  have hsq : (dot α ε) ^ 2 ≤ ∑ i : Fin n, (ε i) ^ 2 := by
    have hcs : (dot α ε) ^ 2 ≤ (dot α α) * (∑ i : Fin n, (ε i) ^ 2) :=
      dot_sq_le_sqNorm_mul α ε
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, (ε i) ^ 2 := by
      exact Finset.sum_nonneg (fun i _ => sq_nonneg (ε i))
    have hmul : (dot α α) * (∑ i : Fin n, (ε i) ^ 2) ≤ 1 * (∑ i : Fin n, (ε i) ^ 2) :=
      mul_le_mul_of_nonneg_right hα hsum_nonneg
    exact le_trans hcs (by simpa using hmul)
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hscaled := mul_le_mul_of_nonneg_left hsq hhalf
  simpa [multiplicativeQuadratic, additiveQuadratic, one_mul] using hscaled

/-- Under normalized weights (`‖α‖² ≤ 1`), the compensatory term is nonnegative. -/
theorem compensatory_nonneg_of_sqNorm_le_one {n : ℕ}
    (α ε : Vec n) (hα : dot α α ≤ 1) :
    0 ≤ compensatoryQuadratic α ε := by
  unfold compensatoryQuadratic
  have hle := multiplicative_le_additive_of_sqNorm_le_one α ε hα
  linarith

end Ndim
end Cost
end IndisputableMonolith

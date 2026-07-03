import Mathlib
import IndisputableMonolith.Relativity.Geometry.Tensor
import IndisputableMonolith.Relativity.Calculus.Derivatives

namespace IndisputableMonolith
namespace Relativity
namespace Geometry

open Calculus

structure MetricTensor where
  g : BilinearForm
  symmetric : ∀ x up low, g x up low = g x up (fun i => if (i : ℕ) = 0 then low 1 else low 0)

@[ext]
lemma MetricTensor.ext (g1 g2 : MetricTensor) (h : g1.g = g2.g) : g1 = g2 := by
  cases g1; cases g2; simp_all

noncomputable def eta : BilinearForm := fun _ _ low =>
  if low 0 = low 1 then (if (low 0 : ℕ) = 0 then -1 else 1) else 0

noncomputable def minkowski_tensor : MetricTensor :=
  { g := eta
    symmetric := by
      intro x up low
      unfold eta
      dsimp
      by_cases h : low 0 = low 1
      · have h_rev : low 1 = low 0 := h.symm
        rw [if_pos h, if_pos h_rev]
        rw [h]
      · have h_rev : low 1 ≠ low 0 := fun heq => h heq.symm
        rw [if_neg h, if_neg h_rev] }

noncomputable def metric_from_rrf (psi : (Fin 4 → ℝ) → ℝ) (k : ℝ) : MetricTensor :=
  { g := fun x _ low =>
      eta x (fun _ => 0) low + k * psi x * (if low 0 = low 1 then 1 else 0)
    symmetric := by
      intro x up low
      unfold eta
      dsimp
      by_cases h : low 0 = low 1
      · have h_rev : low 1 = low 0 := h.symm
        rw [if_pos h, if_pos h, if_pos h_rev, if_pos h_rev]
        rw [h]
      · have h_rev : low 1 ≠ low 0 := fun heq => h heq.symm
        rw [if_neg h, if_neg h, if_neg h_rev, if_neg h_rev] }

noncomputable def metric_to_matrix (g : MetricTensor) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => g.g x (fun _ => 0) (fun k => if (k : ℕ) = 0 then i else j)

/-- The metric matrix is symmetric because the metric tensor is symmetric. -/
lemma metric_to_matrix_symmetric (g : MetricTensor) (x : Fin 4 → ℝ) :
    (metric_to_matrix g x).transpose = metric_to_matrix g x := by
  ext i j
  unfold metric_to_matrix Matrix.transpose
  dsimp
  -- Apply the metric tensor symmetry: g x up low = g x up (swap low)
  have h := g.symmetric x (fun _ => 0) (fun k => if (k : ℕ) = 0 then j else i)
  -- The RHS evaluates to (fun k => if k.val = 0 then i else j) since 1 ≠ 0 and 0 = 0
  simp only [Fin.val_one, Fin.val_zero, one_ne_zero, ite_false, ite_true] at h
  exact h

noncomputable def metric_det (g : MetricTensor) (x : Fin 4 → ℝ) : ℝ :=
  (metric_to_matrix g x).det

noncomputable def inverse_metric (g : MetricTensor) : ContravariantBilinear :=
  fun x up _ =>
    (metric_to_matrix g x)⁻¹ (up 0) (up 1)

/-- Inverse Minkowski metric components. -/
lemma inverse_minkowski_apply (x : Fin 4 → ℝ) (μ ν : Fin 4) :
    inverse_metric minkowski_tensor x (fun i => if (i : ℕ) = 0 then μ else ν) (fun _ => 0) =
    if μ = ν then (if (μ : ℕ) = 0 then -1 else 1) else 0 := by
  unfold inverse_metric
  dsimp
  have h_mat : metric_to_matrix minkowski_tensor x = Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) = 0 then (-1 : ℝ) else 1) := by
    ext i j
    unfold metric_to_matrix minkowski_tensor eta
    dsimp
    by_cases h : i = j
    · rw [if_pos h, h]
      simp
    · rw [if_neg h]
      simp [h]
  rw [h_mat]
  have h_inv : (Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) = 0 then (-1 : ℝ) else 1))⁻¹ =
               Matrix.diagonal (fun i : Fin 4 => if (i : ℕ) = 0 then (-1 : ℝ) else 1) := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    rw [Matrix.one_apply]
    unfold Matrix.diagonal
    dsimp
    by_cases h : i = j
    · rw [if_pos h]
      split_ifs <;> norm_num
    · rw [if_neg h]
      simp [h]
  rw [h_inv]
  unfold Matrix.diagonal
  dsimp

lemma finset_sum_fin_4 {α : Type*} [AddCommMonoid α] (f : Fin 4 → α) :
    Finset.sum Finset.univ f = f 0 + f 1 + f 2 + f 3 := by
  have : Finset.univ = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide
  rw [this]
  simp
  abel

/-- Squared gradient helper for Minkowski metric. -/
lemma gradient_squared_minkowski_sum (grad : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    Finset.sum Finset.univ (fun μ => Finset.sum Finset.univ (fun ν =>
      inverse_metric minkowski_tensor x (fun i => if (i : ℕ) = 0 then μ else ν) (fun _ => 0) *
      grad μ * grad ν)) =
    -(grad 0)^2 + (grad 1)^2 + (grad 2)^2 + (grad 3)^2 := by
  rw [finset_sum_fin_4]
  simp only [finset_sum_fin_4, inverse_minkowski_apply]
  simp
  ring

end Geometry
end Relativity
end IndisputableMonolith

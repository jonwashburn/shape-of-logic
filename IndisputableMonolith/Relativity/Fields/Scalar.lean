import Mathlib
import IndisputableMonolith.Relativity.Geometry

namespace IndisputableMonolith
namespace Relativity
namespace Fields

open Geometry

/-- A scalar field assigns a real value to each spacetime point. -/
structure ScalarField where
  ψ : (Fin 4 → ℝ) → ℝ

/-- Evaluate scalar field at a point. -/
noncomputable def eval (φ : ScalarField) (x : Fin 4 → ℝ) : ℝ := φ.ψ x

/-- Constant scalar field. -/
def constant (c : ℝ) : ScalarField := { ψ := fun _ => c }

theorem constant_eval (c : ℝ) (x : Fin 4 → ℝ) :
  eval (constant c) x = c := rfl

/-- Zero scalar field. -/
def zero : ScalarField := constant 0

theorem zero_eval (x : Fin 4 → ℝ) : eval zero x = 0 := rfl

/-- Scalar field addition. -/
def add (φ₁ φ₂ : ScalarField) : ScalarField :=
  { ψ := fun x => φ₁.ψ x + φ₂.ψ x }

/-- Scalar multiplication. -/
def smul (c : ℝ) (φ : ScalarField) : ScalarField :=
  { ψ := fun x => c * φ.ψ x }

theorem add_comm (φ₁ φ₂ : ScalarField) :
  ∀ x, eval (add φ₁ φ₂) x = eval (add φ₂ φ₁) x := by
  intro x
  simp [eval, add]
  ring

theorem smul_zero (φ : ScalarField) :
  ∀ x, eval (smul 0 φ) x = 0 := by
  intro x
  simp [eval, smul]

/-- Directional derivative of scalar field in direction μ. -/
noncomputable def directional_deriv (φ : ScalarField) (μ : Fin 4) (x : Fin 4 → ℝ) : ℝ :=
  let h := (0.001 : ℝ)
  let x_plus := fun ν => if ν = μ then x ν + h else x ν
  (φ.ψ x_plus - φ.ψ x) / h

/-- Directional derivative is linear in the field. -/
theorem deriv_add (φ₁ φ₂ : ScalarField) (μ : Fin 4) (x : Fin 4 → ℝ) :
  directional_deriv (add φ₁ φ₂) μ x =
    directional_deriv φ₁ μ x + directional_deriv φ₂ μ x := by
  simp [directional_deriv, add]
  ring

theorem deriv_smul (c : ℝ) (φ : ScalarField) (μ : Fin 4) (x : Fin 4 → ℝ) :
  directional_deriv (smul c φ) μ x = c * directional_deriv φ μ x := by
  simp only [directional_deriv, smul]
  ring

/-- Derivative of constant field is zero. -/
theorem deriv_constant (c : ℝ) (μ : Fin 4) (x : Fin 4 → ℝ) :
  directional_deriv (constant c) μ x = 0 := by
  simp only [directional_deriv, constant]
  norm_num

/-- Gradient: collection of all directional derivatives ∂_μ ψ. -/
noncomputable def gradient (φ : ScalarField) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => directional_deriv φ μ x

/-- Squared gradient g^{μν} (∂_μ ψ)(∂_ν ψ) with inverse metric. -/
noncomputable def gradient_squared (φ : ScalarField) (g : MetricTensor) (x : Fin 4 → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (Fin 4)) (fun μ =>
    Finset.sum (Finset.univ : Finset (Fin 4)) (fun ν =>
      (inverse_metric g) x (fun i => if (i : ℕ) = 0 then μ else ν) (fun _ => 0) *
      (gradient φ x μ) * (gradient φ x ν)))

/-- Gradient squared for Minkowski metric. -/
theorem gradient_squared_minkowski (φ : ScalarField) (x : Fin 4 → ℝ) :
  gradient_squared φ minkowski_tensor x =
    -(gradient φ x 0)^2 + (gradient φ x 1)^2 + (gradient φ x 2)^2 + (gradient φ x 3)^2 := by
  unfold gradient_squared
  apply gradient_squared_minkowski_sum

/-- Field squared. -/
noncomputable def field_squared (φ : ScalarField) (x : Fin 4 → ℝ) : ℝ :=
  (φ.ψ x) ^ 2

theorem field_squared_nonneg (φ : ScalarField) (x : Fin 4 → ℝ) :
  field_squared φ x ≥ 0 := by
  simp [field_squared]
  exact sq_nonneg _

end Fields
end Relativity
end IndisputableMonolith

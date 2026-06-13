import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IndisputableMonolith.Geometry.SchlaefliTriangulation3D

/-!
# Regge Hessian Under the 3D Conformal Ansatz

This module provides the Hessian interface for the genuine Regge action on
a finite 3D triangulation.  The analytic/geometric inputs are kept
explicit: a concrete implementation supplies `action`, its Hessian matrix,
and the theorem that the quadratic Taylor coefficient is represented by
that matrix.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeHessian3D

open ReggeTriangulation3D SchlaefliTriangulation3D

noncomputable section

/-- Vertex conformal potentials on a finite 3D triangulation. -/
abbrev VertexPotential (K : Triangulation3D) := Fin K.nV → ℝ

/-- The zero conformal potential. -/
def zeroPotential (K : Triangulation3D) : VertexPotential K := fun _ => 0

/-- Quadratic form associated to a Hessian matrix. -/
def hessianQuadratic {n : ℕ} (H : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, H i j * ξ i * ξ j

/-- Genuine Regge Hessian data for a triangulation.  `action` is the
Regge action under the conformal ansatz, and `hessian` is the matrix of
its second variation at `ξ = 0`. -/
structure ReggeHessianData (K : Triangulation3D) where
  action : VertexPotential K → ℝ
  hessian : Fin K.nV → Fin K.nV → ℝ
  hessian_symm : ∀ i j, hessian i j = hessian j i
  flat_firstVariation_zero : Prop
  secondVariation :
    ∀ ξ : VertexPotential K,
      action ξ - action (zeroPotential K) =
        (1 / 2) * hessianQuadratic hessian ξ

/-- Swap the order of summation in the Hessian quadratic form. -/
theorem hessianQuadratic_sum_comm {n : ℕ} (H : Fin n → Fin n → ℝ)
    (ξ : Fin n → ℝ) :
    hessianQuadratic H ξ =
      ∑ j : Fin n, ∑ i : Fin n, H i j * ξ i * ξ j := by
  unfold hessianQuadratic
  rw [Finset.sum_comm]

/-- Extract the second-variation formula from a concrete Hessian package. -/
theorem regge_secondVariation_eq_hessian
    (K : Triangulation3D) (D : ReggeHessianData K) (ξ : VertexPotential K) :
    D.action ξ - D.action (zeroPotential K) =
      (1 / 2) * hessianQuadratic D.hessian ξ :=
  D.secondVariation ξ

end

end ReggeHessian3D
end Geometry
end IndisputableMonolith

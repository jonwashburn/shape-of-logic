import Mathlib
import IndisputableMonolith.Constants.LambdaRecDerivation
import IndisputableMonolith.Foundation.JCostHessianC7
import IndisputableMonolith.Geometry.ReggeActionConcrete

/-!
# Curvature Cost Form

This module is the M2B bridge from the living plan
`plans/Regge_To_JCurv_CostForm_Closure_Plan_20260617.html`.

It records two facts.

1. The bulk Regge/Dirichlet quadratic cannot be the source of the one-cell
   curvature cost under a uniform conformal scale: constant vertex potentials
   are graph-Laplacian zero modes.
2. The boundary angle-defect cost has a theorem-tier quadratic form:
   the local J-cost Hessian coefficient is `1`, and the Gauss-Bonnet defect
   coefficient is `χ(∂Q₃) = 2`, so the quadratic boundary cost is `2 λ²`.

Honest boundary: the theorem below closes the quadratic FORM used by
`J_curv`; it does not claim the full nonlinear expression `Jcost (1 + λ)` is
exactly `λ²`. In fact `Jcost (1 + λ) = λ² / (2(1+λ))` away from `λ = -1`.
The theorem-grade statement is the Hessian/quadratic-form statement.
-/

namespace IndisputableMonolith
namespace Constants
namespace CurvatureCostForm

open Geometry
open Geometry.ReggeActionConcrete
open Geometry.ReggeHessian3D
open Geometry.ReggeTriangulation3D
open Geometry.Triangulation3DConsistency

noncomputable section

/-! ## M1: bulk Regge uniform-scale zero mode -/

/-- Constant vertex potentials are zero modes of the canonical Dirichlet
energy. This is the formal reason the bulk Regge Hessian does not carry the
single-cell uniform-scale curvature cost: the Dirichlet quadratic only sees
differences `ξ i - ξ j`. -/
theorem canonicalDirichletEnergy_constant_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K) (c : ℝ) :
    canonicalDirichletEnergy K hK (fun _ : Fin K.nV => c) = 0 := by
  unfold canonicalDirichletEnergy
  simp

/-! ## M2B: boundary angle-defect J-cost quadratic form -/

open LambdaRecDerivation

/-- Boundary Gauss-Bonnet coefficient of the one-cell curvature cost:
total angular defect in units of one full turn. -/
abbrev boundaryDefectCoefficient : ℝ :=
  curvatureCoefficient

/-- The boundary coefficient is the Euler characteristic of the cube boundary. -/
theorem boundaryDefectCoefficient_eq_euler_char :
    boundaryDefectCoefficient = (euler_S2 : ℝ) :=
  curvatureCoefficient_eq_euler_char

/-- The local J-cost Hessian coefficient is `1`. This imports the exact
local-algebra theorem `J(1+ε) = ε² / (2(1+ε))` through its standard Hessian
normalization. -/
theorem localJCostHessianCoefficient_eq_one :
    Foundation.JCostHessianC7.jcostHessianCoefficient = 1 :=
  Foundation.JCostHessianC7.jcostHessianCoefficient_eq_one

/-- Boundary curvature-cost quadratic form: Gauss-Bonnet defect coefficient
times the J-cost Hessian coefficient times `λ²`. -/
def boundaryCurvatureQuadraticCost (lam : ℝ) : ℝ :=
  boundaryDefectCoefficient *
    Foundation.JCostHessianC7.jcostHessianCoefficient *
      lam ^ (2 : ℕ)

/-- The boundary angle-defect J-cost quadratic form is exactly `2 λ²`.

This is the form-level closure: the `2` comes from Gauss-Bonnet
(`χ(∂Q₃) = 2`) and the quadratic dependence comes from the Hessian of the
canonical reciprocal cost at equilibrium. -/
theorem boundaryCurvatureQuadraticCost_eq (lam : ℝ) :
    boundaryCurvatureQuadraticCost lam = 2 * lam ^ (2 : ℕ) := by
  unfold boundaryCurvatureQuadraticCost boundaryDefectCoefficient
  rw [curvatureCoefficient_eq_euler_char, localJCostHessianCoefficient_eq_one]
  norm_num [euler_S2]

/-- The existing `J_curv` definition agrees with the theorem-derived boundary
quadratic form. This isolates the only intended meaning of `J_curv`: it is the
quadratic boundary angle-defect J-cost, not the bulk Regge Dirichlet energy and
not the full nonlinear `Jcost (1+λ)`. -/
theorem J_curv_eq_boundaryCurvatureQuadraticCost (lam : ℝ) :
    LambdaRecDerivation.J_curv lam = boundaryCurvatureQuadraticCost lam := by
  rw [LambdaRecDerivation.J_curv_derivation, boundaryCurvatureQuadraticCost_eq]

/-- M2B certificate: bulk uniform scaling is a Regge zero mode, while the
boundary angle-defect quadratic cost equals the existing `J_curv`. -/
structure CurvatureCostFormCert where
  bulk_uniform_scale_zero :
    ∀ (K : Triangulation3D) (hK : IncidenceConsistent K) (c : ℝ),
      canonicalDirichletEnergy K hK (fun _ : Fin K.nV => c) = 0
  boundary_cost_eq :
    ∀ lam : ℝ, LambdaRecDerivation.J_curv lam = boundaryCurvatureQuadraticCost lam
  boundary_cost_closed :
    ∀ lam : ℝ, boundaryCurvatureQuadraticCost lam = 2 * lam ^ (2 : ℕ)
  coefficient_is_euler :
    boundaryDefectCoefficient = (euler_S2 : ℝ)
  j_hessian_one :
    Foundation.JCostHessianC7.jcostHessianCoefficient = 1

/-- The curvature-cost form certificate is inhabited. -/
def curvatureCostFormCert : CurvatureCostFormCert where
  bulk_uniform_scale_zero := canonicalDirichletEnergy_constant_zero
  boundary_cost_eq := J_curv_eq_boundaryCurvatureQuadraticCost
  boundary_cost_closed := boundaryCurvatureQuadraticCost_eq
  coefficient_is_euler := boundaryDefectCoefficient_eq_euler_char
  j_hessian_one := localJCostHessianCoefficient_eq_one

end

end CurvatureCostForm
end Constants
end IndisputableMonolith

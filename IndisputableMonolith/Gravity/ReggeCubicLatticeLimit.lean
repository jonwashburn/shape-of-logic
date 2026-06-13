import Mathlib
import IndisputableMonolith.Geometry.ReggeActionSecondVariation
import IndisputableMonolith.Gravity.CubicReggeConvergence

/-!
# Cubic-Lattice Limit for the Second-Order Regge Action

The general CMS theorem gives a weak curvature-measure convergence statement,
not a plain `O(a^2)` action estimate.  The `O(a^2)` statement belongs to the
regular weak-field cubic-lattice case.  This module isolates that special
case for the canonical second-order Regge action.
-/

namespace IndisputableMonolith
namespace Gravity
namespace ReggeCubicLatticeLimit

open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open Geometry.Triangulation3DConsistency
open Geometry.ReggeActionConcrete

noncomputable section

/-- A regular cubic-lattice comparison model for the canonical second-order
Regge action. -/
structure RegularCubicLatticeModel
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  latticeSpacing : ℝ
  spacing_pos : 0 < latticeSpacing
  continuumAction : VertexPotential K → ℝ
  errorConstant : ℝ
  errorConstant_nonneg : 0 ≤ errorConstant
  secondOrder_action_error :
    ∀ ξ : VertexPotential K,
      |reggeActionSecondOrder K hK (canonicalReggeHessian K hK) ξ -
        continuumAction ξ| ≤ errorConstant * latticeSpacing ^ (2 : ℕ)

/-- The second-order Regge action has an `O(a^2)` cubic-lattice continuum
limit in the supplied regular lattice model. -/
def ReggeSecondOrderCubicLatticeLimit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (M : RegularCubicLatticeModel K hK) : Prop :=
  ∀ ξ : VertexPotential K,
    |reggeActionSecondOrder K hK (canonicalReggeHessian K hK) ξ -
      M.continuumAction ξ| ≤ M.errorConstant * M.latticeSpacing ^ (2 : ℕ)

/-- Named input connecting a concrete regular triangulation model to the
canonical second-order Regge action. -/
structure ReggeCubicLatticeLimitInput
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  model : RegularCubicLatticeModel K hK
  limit_estimate : ReggeSecondOrderCubicLatticeLimit K hK model

/-- Physical six-tet cubic Dirichlet model data.  This is the target class
for the real cubic-lattice instance: prove that the canonical second-order
Regge action on the six-tetrahedra-per-cube triangulation is the finite-
difference Dirichlet action, then supply the O(a^2) estimate. -/
structure PhysicalSixTetCubicDirichletModel
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  regularModel : RegularCubicLatticeModel K hK
  sixTetCubicDecomposition : Prop
  canonicalHessian_is_dirichlet : Prop
  finiteDifferenceEstimate :
    ReggeSecondOrderCubicLatticeLimit K hK regularModel

def cubicLatticeLimitInput_of_physicalSixTetModel
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (M : PhysicalSixTetCubicDirichletModel K hK) :
    ReggeCubicLatticeLimitInput K hK where
  model := M.regularModel
  limit_estimate := M.finiteDifferenceEstimate

/-- Phase-G cubic-lattice `O(a^2)` continuum-limit theorem for the canonical
second-order Regge action. -/
theorem reggeActionSecondOrder_cubic_lattice_limit
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_limit : ReggeCubicLatticeLimitInput K hK) :
    ReggeSecondOrderCubicLatticeLimit K hK h_limit.model :=
  h_limit.limit_estimate

/-- A family of cubic-lattice comparison models converges pointwise whenever
its certified `O(a^2)` error envelope tends to zero along the refinement
parameter. -/
theorem reggeSecondOrderCubicLatticeLimit_error_vanishes_along_models
    {α : Type*} {l : Filter α}
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (M : α → RegularCubicLatticeModel K hK)
    (hLimit : ∀ t : α, ReggeSecondOrderCubicLatticeLimit K hK (M t))
    (hEnvelope :
      Filter.Tendsto
        (fun t : α => (M t).errorConstant * (M t).latticeSpacing ^ (2 : ℕ))
        l (nhds 0))
    (ξ : VertexPotential K) :
    Filter.Tendsto
      (fun t : α =>
        |reggeActionSecondOrder K hK (canonicalReggeHessian K hK) ξ -
          (M t).continuumAction ξ|)
      l (nhds 0) := by
  apply squeeze_zero
  · intro t
    exact abs_nonneg _
  · intro t
    exact hLimit t ξ
  · exact hEnvelope

/-- The existing one-dimensional finite-difference theorem is the analytic
ingredient used in the cubic-lattice model. -/
theorem finite_difference_second_order_estimate
    (f : ℝ → ℝ) (x a : ℝ) (ha : a ≠ 0) (hf : ContDiff ℝ 4 f) :
    ∃ C : ℝ, 0 ≤ C ∧
      |(f (x + a) + f (x - a) - 2 * f x) / a ^ 2 -
        deriv (deriv f) x| ≤ C * a ^ 2 :=
  CubicReggeConvergence.weak_field_error_estimate f x a ha hf

/-- Exact comparison model: the continuum action is chosen to be the
canonical second-order Regge action itself, so the error constant is zero.

This is not the physical regular cubic-lattice continuum model.  It is a
sanity-check instance showing that `RegularCubicLatticeModel` and
`ReggeCubicLatticeLimitInput` are constructible without further caller data.
The real cubic-lattice instance still has to identify this action with the
finite-difference Dirichlet action. -/
def exactSecondOrderComparisonModel
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (a : ℝ) (ha : 0 < a) :
    RegularCubicLatticeModel K hK where
  latticeSpacing := a
  spacing_pos := ha
  continuumAction := reggeActionSecondOrder K hK (canonicalReggeHessian K hK)
  errorConstant := 0
  errorConstant_nonneg := le_rfl
  secondOrder_action_error := by
    intro ξ
    simp

def exactSecondOrderCubicLatticeLimitInput
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (a : ℝ) (ha : 0 < a) :
    ReggeCubicLatticeLimitInput K hK where
  model := exactSecondOrderComparisonModel K hK a ha
  limit_estimate := by
    intro ξ
    simp [exactSecondOrderComparisonModel]

end

end ReggeCubicLatticeLimit
end Gravity
end IndisputableMonolith

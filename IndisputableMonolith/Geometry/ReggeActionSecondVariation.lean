import Mathlib
import IndisputableMonolith.Geometry.ReggeActionFirstVariation

/-!
# Second Variation and Cubic Remainder of the Nonlinear Regge Action

This module states the nonlinear second-variation and cubic-remainder targets
in a form that is usable now.  The lower-level calculation is the large
Cayley-Menger/arccos chain-rule expansion; until that calculation is fully
materialized, the required analytic facts live in named input structures.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeActionSecondVariation

open ReggeTriangulation3D
open ReggeHessian3D
open Triangulation3DConsistency
open ReggeActionConcrete
open ReggeActionSmoothness
open ReggeActionFirstVariation

noncomputable section

/-- The line through the flat potential in direction `ξ`. -/
def linePotential (K : Triangulation3D) (ξ : VertexPotential K) (t : ℝ) :
    VertexPotential K :=
  fun i => t * ξ i

theorem linePotential_zero
    (K : Triangulation3D) (ξ : VertexPotential K) :
    linePotential K ξ 0 = zeroPotential K := by
  funext i
  simp [linePotential, zeroPotential]

/-- A one-variable second derivative statement used for directional Hessian
comparisons. -/
def HasSecondDerivAt (f : ℝ → ℝ) (d2 x : ℝ) : Prop :=
  HasDerivAt (fun t : ℝ => deriv f t) d2 x

theorem hessianQuadratic_linePotential
    (K : Triangulation3D) (H : Fin K.nV → Fin K.nV → ℝ)
    (ξ : VertexPotential K) (t : ℝ) :
    hessianQuadratic H (linePotential K ξ t) =
      t ^ 2 * hessianQuadratic H ξ := by
  unfold hessianQuadratic linePotential
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

theorem hessianQuadratic_along_line_hasSecondDerivAt_zero
    (K : Triangulation3D) (H : Fin K.nV → Fin K.nV → ℝ)
    (ξ : VertexPotential K) :
    HasSecondDerivAt
      (fun t : ℝ => (1 / 2) * hessianQuadratic H (linePotential K ξ t))
      (hessianQuadratic H ξ) 0 := by
  unfold HasSecondDerivAt
  have hquad :
      (fun t : ℝ => (1 / 2) * hessianQuadratic H (linePotential K ξ t)) =
        fun t : ℝ => (hessianQuadratic H ξ / 2) * t ^ 2 := by
    funext t
    rw [hessianQuadratic_linePotential]
    ring
  rw [hquad]
  have hderiv :
      deriv (fun t : ℝ => (hessianQuadratic H ξ / 2) * t ^ 2) =
        fun t : ℝ => hessianQuadratic H ξ * t := by
    ext t
    have h :=
      ((hasDerivAt_id t).pow 2).const_mul (hessianQuadratic H ξ / 2)
    have h' : HasDerivAt
        (fun t : ℝ => (hessianQuadratic H ξ / 2) * t ^ 2)
        (hessianQuadratic H ξ * t) t := by
      simpa [id, two_mul, mul_comm, mul_left_comm, mul_assoc] using h
    exact h'.deriv
  rw [hderiv]
  simpa using (hasDerivAt_id 0).const_mul (hessianQuadratic H ξ)

/-- The nonlinear Regge action restricted to a one-dimensional conformal
line through the flat potential. -/
def actionAlongLine
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (ξ : VertexPotential K) (t : ℝ) : ℝ :=
  reggeAction K hK (linePotential K ξ t)

/-- The nonlinear action has the canonical incidence Hessian as its second
variation at the flat potential, tested on every conformal line. -/
def CanonicalHessianSecondVariationAtZero
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasSecondDerivAt (actionAlongLine K hK ξ)
      (hessianQuadratic (canonicalReggeHessian K hK) ξ) 0

/-- Named second-variation input for the full nonlinear action. -/
structure ReggeActionSecondVariationInput
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_h_flat : FlatConfiguration K hK) where
  canonical_secondVariation : CanonicalHessianSecondVariationAtZero K hK

def reggeActionSecondVariationInput_of_directionalSecondVariation
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hSecond : CanonicalHessianSecondVariationAtZero K hK) :
    ReggeActionSecondVariationInput K hK h_flat where
  canonical_secondVariation := hSecond

/-- Phase-D second-variation theorem, conditional on the named nonlinear
second-variation input. -/
theorem reggeAction_secondVariation_eq_canonicalHessian
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (h_second : ReggeActionSecondVariationInput K hK h_flat) :
    CanonicalHessianSecondVariationAtZero K hK :=
  h_second.canonical_secondVariation

/-- The canonical nonlinear remainder has zero second variation at the flat
potential. -/
def CanonicalRemainderSecondVariationZero
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∀ ξ : VertexPotential K,
    HasSecondDerivAt
      (fun t : ℝ =>
        reggeActionRemainder K hK (canonicalReggeHessian K hK)
          (linePotential K ξ t))
      0 0

structure ReggeActionRemainderSecondVariationInput
    (K : Triangulation3D) (hK : IncidenceConsistent K) where
  remainder_secondVariation_zero :
    CanonicalRemainderSecondVariationZero K hK

theorem reggeActionRemainder_secondVariation_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_rem : ReggeActionRemainderSecondVariationInput K hK) :
    CanonicalRemainderSecondVariationZero K hK :=
  h_rem.remainder_secondVariation_zero

/-- Local cubic bound for the canonical nonlinear Taylor remainder. -/
def LocalCubicRemainderBound
    (K : Triangulation3D) (hK : IncidenceConsistent K) : Prop :=
  ∃ (r C : ℝ), 0 < r ∧ 0 ≤ C ∧
    ∀ ξ : VertexPotential K, ‖ξ‖ < r →
      ‖reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ‖ ≤
        C * ‖ξ‖ ^ (3 : ℕ)

/-- Named Taylor-remainder input.  This is the exact place where Mathlib's
multivariate Taylor theorem, or an `IsBigO` fallback, should be connected. -/
structure ReggeActionCubicRemainderInput
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (_h_flat : FlatConfiguration K hK) where
  cubic_bound : LocalCubicRemainderBound K hK

def reggeActionCubicRemainderInput_of_bound
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hBound : LocalCubicRemainderBound K hK) :
    ReggeActionCubicRemainderInput K hK h_flat where
  cubic_bound := hBound

/-- A strong but useful sanity constructor: if the canonical remainder is
identically zero, it satisfies the local cubic bound with constant zero. -/
def reggeActionCubicRemainderInput_of_identically_zero
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (hZero :
      ∀ ξ : VertexPotential K,
        reggeActionRemainder K hK (canonicalReggeHessian K hK) ξ = 0) :
    ReggeActionCubicRemainderInput K hK h_flat where
  cubic_bound := by
    refine ⟨1, 0, by norm_num, le_rfl, ?_⟩
    intro ξ _hξ
    rw [hZero ξ]
    simp

/-- Phase-E cubic remainder theorem, conditional on the named Taylor input. -/
theorem reggeActionRemainder_cubic_bound
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (h_flat : FlatConfiguration K hK)
    (h_cubic : ReggeActionCubicRemainderInput K hK h_flat) :
    LocalCubicRemainderBound K hK :=
  h_cubic.cubic_bound

end

end ReggeActionSecondVariation
end Geometry
end IndisputableMonolith

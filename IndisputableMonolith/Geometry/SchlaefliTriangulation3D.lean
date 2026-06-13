import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import IndisputableMonolith.Geometry.SchlaefliTetrahedron
import IndisputableMonolith.Geometry.ReggeTriangulation3D

/-!
# Schläfli Identity for Finite 3D Triangulations

The global 3D Schläfli cancellation is the finite sum of the local
tetrahedral Schläfli identities over top-dimensional simplices.
-/

namespace IndisputableMonolith
namespace Geometry
namespace SchlaefliTriangulation3D

open ReggeTriangulation3D SchlaefliTetrahedron

noncomputable section

/-- Local Schläfli derivative data on every tetrahedron of a finite
triangulation. -/
structure TriangulationSchlaefliData (K : Triangulation3D) where
  tetData : ∀ τ : Fin K.nT, TetraSchlaefliDerivativeData (K.tet τ)

/-- The global Schläfli left-hand side, summed over tetrahedra and local
tetrahedral edges. -/
def globalSchlaefliLHS (K : Triangulation3D)
    (D : TriangulationSchlaefliData K) (e' : Fin 6) : ℝ :=
  ∑ τ : Fin K.nT,
    ∑ e : Fin 6,
      Real.sqrt ((K.tet τ).sqEdge e) * (D.tetData τ).dihedralDeriv e e'

/-- The global Schläfli right-hand side: the Euclidean angle-variation term
vanishes. -/
def globalSchlaefliRHS (K : Triangulation3D)
    (_D : TriangulationSchlaefliData K) (_e' : Fin 6) : ℝ :=
  0

/-- Summing local tetrahedral Schläfli identities gives the global finite
triangulation identity. -/
theorem global_schlaefli_of_local
    (K : Triangulation3D) (D : TriangulationSchlaefliData K) (e' : Fin 6) :
    globalSchlaefliLHS K D e' = globalSchlaefliRHS K D e' := by
  unfold globalSchlaefliLHS globalSchlaefliRHS
  have hlocal : ∀ τ : Fin K.nT,
      (∑ e : Fin 6,
        Real.sqrt ((K.tet τ).sqEdge e) * (D.tetData τ).dihedralDeriv e e')
        = 0 := by
    intro τ
    exact (D.tetData τ).schlaefli e'
  simp_rw [hlocal]
  simp

end

end SchlaefliTriangulation3D
end Geometry
end IndisputableMonolith

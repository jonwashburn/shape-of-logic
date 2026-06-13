import IndisputableMonolith.Geometry.SchlaefliTriangulation3D
import IndisputableMonolith.Geometry.SchlaefliTetrahedronProof

/-!
# Incidence-Consistent 3D Regge Triangulations

This module strengthens the abstract `Triangulation3D` scaffold with the
incidence and local-Schläfli data needed to construct global Schläfli
cancellation.
-/

namespace IndisputableMonolith
namespace Geometry
namespace Triangulation3DConsistency

open ReggeTriangulation3D
open SchlaefliTriangulation3D
open SchlaefliTetrahedron
open SchlaefliTetrahedronProof

noncomputable section

/-- Strong incidence consistency for the current 3D Regge scaffold.

The first fields state that local tetrahedral edge slots agree with global
edge endpoints up to orientation.  The last field is the local closed-form
Schläfli proof required to build global Schläfli without caller-supplied
`TriangulationSchlaefliData`. -/
structure IncidenceConsistent (K : Triangulation3D) where
  globalSqEdge : Fin K.nE → ℝ
  edgeInTet_vertices :
    ∀ e τ f, K.edgeInTet e τ = some f →
      let ev := K.edgeVerts e
      let tv := ReggeRigorousFoundation.edgeVertices f
      (K.tetVerts τ tv.1 = ev.1 ∧ K.tetVerts τ tv.2 = ev.2) ∨
        (K.tetVerts τ tv.1 = ev.2 ∧ K.tetVerts τ tv.2 = ev.1)
  local_sqEdge_eq_global :
    ∀ e τ f, K.edgeInTet e τ = some f →
      (K.tet τ).sqEdge f = globalSqEdge e
  localEdge_complete :
    ∀ τ f, ∃ e : Fin K.nE, K.edgeInTet e τ = some f
  local_schlaefli :
    ∀ τ : Fin K.nT, TetraSchlaefliClosedEquation (K.tet τ)

/-- Pure geometric incidence consistency, without storing local Schläfli
proofs as fields.  This is the right input once the tetrahedral Schläfli
theorem is available globally. -/
structure IncidenceGeometry (K : Triangulation3D) where
  globalSqEdge : Fin K.nE → ℝ
  edgeInTet_vertices :
    ∀ e τ f, K.edgeInTet e τ = some f →
      let ev := K.edgeVerts e
      let tv := ReggeRigorousFoundation.edgeVertices f
      (K.tetVerts τ tv.1 = ev.1 ∧ K.tetVerts τ tv.2 = ev.2) ∨
        (K.tetVerts τ tv.1 = ev.2 ∧ K.tetVerts τ tv.2 = ev.1)
  local_sqEdge_eq_global :
    ∀ e τ f, K.edgeInTet e τ = some f →
      (K.tet τ).sqEdge f = globalSqEdge e
  localEdge_complete :
    ∀ τ f, ∃ e : Fin K.nE, K.edgeInTet e τ = some f

/-- A global edge length from the incidence-level squared-edge chart. -/
def globalEdgeLength (K : Triangulation3D) (hK : IncidenceConsistent K)
    (e : Fin K.nE) : ℝ :=
  Real.sqrt (hK.globalSqEdge e)

/-- Local tetrahedral squared-edge slots agree with the global squared-edge
chart whenever the incidence map identifies them. -/
theorem localSqEdge_eq_globalSqEdge
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (e : Fin K.nE) (τ : Fin K.nT) (f : Fin 6)
    (h : K.edgeInTet e τ = some f) :
    (K.tet τ).sqEdge f = hK.globalSqEdge e :=
  hK.local_sqEdge_eq_global e τ f h

/-- The local edge length at any incident tetrahedral edge equals the global
edge length determined by the consistency chart. -/
theorem localEdgeLength_eq_globalEdgeLength
    (K : Triangulation3D) (hK : IncidenceConsistent K)
    (e : Fin K.nE) (τ : Fin K.nT) (f : Fin 6)
    (h : K.edgeInTet e τ = some f) :
    Real.sqrt ((K.tet τ).sqEdge f) = globalEdgeLength K hK e := by
  unfold globalEdgeLength
  rw [localSqEdge_eq_globalSqEdge K hK e τ f h]

/-- Construct local Schläfli data on every tetrahedron from the incidence
mixin's closed-form local Schläfli proof. -/
def triangulationSchlaefliData_of_incidence
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    TriangulationSchlaefliData K where
  tetData := fun τ =>
    tetraSchlaefliDerivativeData_closedForm (K.tet τ) (hK.local_schlaefli τ)

/-- Strong incidence plus local closed-form Schläfli gives global Schläfli. -/
theorem global_schlaefli_from_incidence
    (K : Triangulation3D) (hK : IncidenceConsistent K) (e' : Fin 6) :
    globalSchlaefliLHS K (triangulationSchlaefliData_of_incidence K hK) e' =
      globalSchlaefliRHS K (triangulationSchlaefliData_of_incidence K hK) e' :=
  global_schlaefli_of_local K (triangulationSchlaefliData_of_incidence K hK) e'

/-- Incidence consistency constructs the global Schläfli data package. -/
theorem nonempty_triangulationSchlaefliData_of_incidence
    (K : Triangulation3D) (hK : IncidenceConsistent K) :
    Nonempty (TriangulationSchlaefliData K) :=
  ⟨triangulationSchlaefliData_of_incidence K hK⟩

/-- Once the local closed-form Schläfli theorem is proved globally, pure
incidence geometry constructs local Schläfli data on every tetrahedron with
no stored local Schläfli field. -/
def triangulationSchlaefliData_of_geometry
    (K : Triangulation3D) (_hK : IncidenceGeometry K)
    (hLocal : SchlaefliTetrahedronClosedFormTarget) :
    TriangulationSchlaefliData K where
  tetData := fun τ =>
    tetraSchlaefliDerivativeData_closedForm (K.tet τ) (hLocal (K.tet τ))

/-- Pure incidence geometry plus the local theorem gives global Schläfli. -/
theorem global_schlaefli_from_geometry
    (K : Triangulation3D) (hK : IncidenceGeometry K)
    (hLocal : SchlaefliTetrahedronClosedFormTarget) (e' : Fin 6) :
    globalSchlaefliLHS K (triangulationSchlaefliData_of_geometry K hK hLocal) e' =
      globalSchlaefliRHS K (triangulationSchlaefliData_of_geometry K hK hLocal) e' :=
  global_schlaefli_of_local K (triangulationSchlaefliData_of_geometry K hK hLocal) e'

end

end Triangulation3DConsistency
end Geometry
end IndisputableMonolith

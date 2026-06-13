import IndisputableMonolith.Geometry.ReggeActionFirstVariation

/-!
# Freudenthal Six-Tetrahedron Cube Triangulation

This module instantiates the incidence bookkeeping class for the standard
Freudenthal decomposition of one unit cube into six tetrahedra, using the
body diagonal from vertex `0` to vertex `7`.

Cube vertex labels are binary coordinates:

* `0 = (0,0,0)`
* `1 = (1,0,0)`
* `2 = (0,1,0)`
* `3 = (1,1,0)`
* `4 = (0,0,1)`
* `5 = (1,0,1)`
* `6 = (0,1,1)`
* `7 = (1,1,1)`

The six tetrahedra are the monotone paths from `0` to `7`.
-/

namespace IndisputableMonolith
namespace Geometry
namespace FreudenthalCubeTriangulation

open ReggeRigorousFoundation
open ReggeTriangulation3D
open Triangulation3DConsistency
open ReggeActionFirstVariation
open SchlaefliTetrahedronProof

noncomputable section

/-- The local squared-edge tuple for every Freudenthal tetrahedron in the unit
cube: three unit step edges, two face diagonals, and one body diagonal. -/
def freudenthalTetSqEdges : CayleyMengerPolynomial.SqEdges
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 1
  | 4 => 2
  | 5 => 1

theorem cm3_freudenthalTetSqEdges :
    CayleyMengerPolynomial.cm3 freudenthalTetSqEdges = 8 := by
  unfold freudenthalTetSqEdges CayleyMengerPolynomial.cm3
  norm_num

/-- A unit-cube Freudenthal tetrahedron is nondegenerate. -/
def freudenthalTet : NonDegenerateTet where
  sqEdge := freudenthalTetSqEdges
  sqEdge_pos := by
    intro i
    fin_cases i <;> norm_num [freudenthalTetSqEdges]
  cm_pos := by
    rw [cm3_freudenthalTetSqEdges]
    norm_num

/-- The 19 unique edges in the Freudenthal triangulation of the unit cube. -/
def edgeVerts : Fin 19 → Fin 8 × Fin 8
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 4)
  | 3 => (0, 3)
  | 4 => (0, 5)
  | 5 => (0, 6)
  | 6 => (0, 7)
  | 7 => (1, 3)
  | 8 => (1, 5)
  | 9 => (1, 7)
  | 10 => (2, 3)
  | 11 => (2, 6)
  | 12 => (2, 7)
  | 13 => (3, 7)
  | 14 => (4, 5)
  | 15 => (4, 6)
  | 16 => (4, 7)
  | 17 => (5, 7)
  | 18 => (6, 7)
  | ⟨n+19, h⟩ => absurd h (by omega)

/-- Squared length of each global edge. -/
def globalSqEdge : Fin 19 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 1
  | 8 => 1
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | ⟨n+19, h⟩ => absurd h (by omega)

/-- The six tetrahedra as vertex lists. -/
def tetVerts : Fin 6 → Fin 4 → Fin 8
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 3
  | 0, 3 => 7
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 5
  | 1, 3 => 7
  | 2, 0 => 0
  | 2, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 7
  | 3, 0 => 0
  | 3, 1 => 2
  | 3, 2 => 6
  | 3, 3 => 7
  | 4, 0 => 0
  | 4, 1 => 4
  | 4, 2 => 5
  | 4, 3 => 7
  | 5, 0 => 0
  | 5, 1 => 4
  | 5, 2 => 6
  | 5, 3 => 7

/-- Chosen global edge for each local tetrahedral edge slot. -/
def localEdgeOf : Fin 6 → Fin 6 → Fin 19
  | 0, 0 => 0
  | 0, 1 => 3
  | 0, 2 => 6
  | 0, 3 => 7
  | 0, 4 => 9
  | 0, 5 => 13
  | 1, 0 => 0
  | 1, 1 => 4
  | 1, 2 => 6
  | 1, 3 => 8
  | 1, 4 => 9
  | 1, 5 => 17
  | 2, 0 => 1
  | 2, 1 => 3
  | 2, 2 => 6
  | 2, 3 => 10
  | 2, 4 => 12
  | 2, 5 => 13
  | 3, 0 => 1
  | 3, 1 => 5
  | 3, 2 => 6
  | 3, 3 => 11
  | 3, 4 => 12
  | 3, 5 => 18
  | 4, 0 => 2
  | 4, 1 => 4
  | 4, 2 => 6
  | 4, 3 => 14
  | 4, 4 => 16
  | 4, 5 => 17
  | 5, 0 => 2
  | 5, 1 => 5
  | 5, 2 => 6
  | 5, 3 => 15
  | 5, 4 => 16
  | 5, 5 => 18

/-- Incidence map from a global edge and tetrahedron to the local edge slot,
if the edge belongs to that tetrahedron. -/
def edgeInTet : Fin 19 → Fin 6 → Option (Fin 6)
  | 0, 0 => some 0
  | 3, 0 => some 1
  | 6, 0 => some 2
  | 7, 0 => some 3
  | 9, 0 => some 4
  | 13, 0 => some 5
  | 0, 1 => some 0
  | 4, 1 => some 1
  | 6, 1 => some 2
  | 8, 1 => some 3
  | 9, 1 => some 4
  | 17, 1 => some 5
  | 1, 2 => some 0
  | 3, 2 => some 1
  | 6, 2 => some 2
  | 10, 2 => some 3
  | 12, 2 => some 4
  | 13, 2 => some 5
  | 1, 3 => some 0
  | 5, 3 => some 1
  | 6, 3 => some 2
  | 11, 3 => some 3
  | 12, 3 => some 4
  | 18, 3 => some 5
  | 2, 4 => some 0
  | 4, 4 => some 1
  | 6, 4 => some 2
  | 14, 4 => some 3
  | 16, 4 => some 4
  | 17, 4 => some 5
  | 2, 5 => some 0
  | 5, 5 => some 1
  | 6, 5 => some 2
  | 15, 5 => some 3
  | 16, 5 => some 4
  | 18, 5 => some 5
  | _, _ => none

/-- The finite Freudenthal cube triangulation. -/
def freudenthalCube : Triangulation3D where
  nV := 8
  nE := 19
  nT := 6
  edgeVerts := edgeVerts
  tetVerts := tetVerts
  edgeInTet := edgeInTet
  tet := fun _ => freudenthalTet

theorem edgeInTet_iff_localEdgeOf
    (e : Fin 19) (τ f : Fin 6) :
    edgeInTet e τ = some f ↔ e = localEdgeOf τ f := by
  fin_cases e <;> fin_cases τ <;> fin_cases f <;>
    simp [edgeInTet, localEdgeOf]

theorem local_sqEdge_eq_global
    (e : Fin 19) (τ f : Fin 6) (h : edgeInTet e τ = some f) :
    freudenthalTet.sqEdge f = globalSqEdge e := by
  fin_cases e <;> fin_cases τ <;> fin_cases f <;>
    simp [edgeInTet, freudenthalTet, freudenthalTetSqEdges, globalSqEdge] at h ⊢

theorem edgeInTet_vertices
    (e : Fin 19) (τ f : Fin 6) (h : edgeInTet e τ = some f) :
      let ev := edgeVerts e
      let tv := ReggeRigorousFoundation.edgeVertices f
      (tetVerts τ tv.1 = ev.1 ∧ tetVerts τ tv.2 = ev.2) ∨
        (tetVerts τ tv.1 = ev.2 ∧ tetVerts τ tv.2 = ev.1) := by
  fin_cases e <;> fin_cases τ <;> fin_cases f <;>
    simp [edgeInTet, edgeVerts, tetVerts, ReggeRigorousFoundation.edgeVertices] at h ⊢

theorem localEdge_complete (τ f : Fin 6) :
    ∃ e : Fin 19, edgeInTet e τ = some f := by
  exact ⟨localEdgeOf τ f, (edgeInTet_iff_localEdgeOf (localEdgeOf τ f) τ f).2 rfl⟩

/-- Incidence consistency for the Freudenthal cube. -/
def freudenthalCube_incidenceConsistent :
    IncidenceConsistent freudenthalCube where
  globalSqEdge := globalSqEdge
  edgeInTet_vertices := by
    intro e τ f h
    exact edgeInTet_vertices e τ f h
  local_sqEdge_eq_global := by
    intro e τ f h
    exact local_sqEdge_eq_global e τ f h
  localEdge_complete := by
    intro τ f
    exact localEdge_complete τ f
  local_schlaefli := by
    intro τ
    exact schlaefliTetrahedronClosedForm freudenthalTet

/-- The Freudenthal cube has the intended unique/no-duplication local edge-slot
partition. -/
def freudenthalCube_edgeSlotPartition :
    IncidenceEdgeSlotPartition freudenthalCube freudenthalCube_incidenceConsistent where
  localEdgeOf := localEdgeOf
  edgeInTet_iff := by
    intro e τ f
    exact edgeInTet_iff_localEdgeOf e τ f

/-- Concrete edge-slot bookkeeping for the Freudenthal six-tetrahedron cube. -/
def freudenthalCube_edgeSlotBookkeeping :
    IncidenceEdgeSlotBookkeeping freudenthalCube freudenthalCube_incidenceConsistent :=
  incidenceEdgeSlotBookkeeping_of_partition
    freudenthalCube freudenthalCube_incidenceConsistent freudenthalCube_edgeSlotPartition

end

end FreudenthalCubeTriangulation
end Geometry
end IndisputableMonolith

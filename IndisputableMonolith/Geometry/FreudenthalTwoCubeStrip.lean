import IndisputableMonolith.Geometry.FreudenthalCubeTriangulation

/-!
# Two-Cube Freudenthal Strip

This module gives the smallest nontrivial multi-cube Freudenthal example:
two unit cubes sharing one square face, each decomposed into six Freudenthal
tetrahedra with compatible face triangulation.

It proves the global local-edge-slot partition after deduplicating the five
shared face edges.  This is the first concrete multi-cube incidence instance
beyond the one-cube sanity check.
-/

namespace IndisputableMonolith
namespace Geometry
namespace FreudenthalTwoCubeStrip

open ReggeRigorousFoundation
open ReggeTriangulation3D
open Triangulation3DConsistency
open ReggeActionFirstVariation
open SchlaefliTetrahedronProof

noncomputable section

abbrev V := Fin 12
abbrev E := Fin 33
abbrev T := Fin 12

/-- The 33 unique global edges in the two-cube Freudenthal strip. -/
def edgeVerts : E → V × V
  | 0 => (0, 1)
  | 1 => (0, 3)
  | 2 => (0, 6)
  | 3 => (0, 4)
  | 4 => (0, 7)
  | 5 => (0, 9)
  | 6 => (0, 10)
  | 7 => (1, 4)
  | 8 => (1, 7)
  | 9 => (1, 10)
  | 10 => (3, 4)
  | 11 => (3, 9)
  | 12 => (3, 10)
  | 13 => (4, 10)
  | 14 => (6, 7)
  | 15 => (6, 9)
  | 16 => (6, 10)
  | 17 => (7, 10)
  | 18 => (9, 10)
  | 19 => (1, 2)
  | 20 => (1, 5)
  | 21 => (1, 8)
  | 22 => (1, 11)
  | 23 => (2, 5)
  | 24 => (2, 8)
  | 25 => (2, 11)
  | 26 => (4, 5)
  | 27 => (4, 11)
  | 28 => (5, 11)
  | 29 => (7, 8)
  | 30 => (7, 11)
  | 31 => (8, 11)
  | 32 => (10, 11)
  | ⟨n+33, h⟩ => absurd h (by omega)

def globalSqEdge : E → ℝ
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
  | 19 => 1
  | 20 => 2
  | 21 => 2
  | 22 => 3
  | 23 => 1
  | 24 => 1
  | 25 => 2
  | 26 => 1
  | 27 => 2
  | 28 => 1
  | 29 => 1
  | 30 => 2
  | 31 => 1
  | 32 => 1
  | ⟨n+33, h⟩ => absurd h (by omega)

/-- Twelve tetrahedra: six in the left cube and six in the right cube. -/
def tetVerts : T → Fin 4 → V
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 4
  | 0, 3 => 10
  | 1, 0 => 0
  | 1, 1 => 1
  | 1, 2 => 7
  | 1, 3 => 10
  | 2, 0 => 0
  | 2, 1 => 3
  | 2, 2 => 4
  | 2, 3 => 10
  | 3, 0 => 0
  | 3, 1 => 3
  | 3, 2 => 9
  | 3, 3 => 10
  | 4, 0 => 0
  | 4, 1 => 6
  | 4, 2 => 7
  | 4, 3 => 10
  | 5, 0 => 0
  | 5, 1 => 6
  | 5, 2 => 9
  | 5, 3 => 10
  | 6, 0 => 1
  | 6, 1 => 2
  | 6, 2 => 5
  | 6, 3 => 11
  | 7, 0 => 1
  | 7, 1 => 2
  | 7, 2 => 8
  | 7, 3 => 11
  | 8, 0 => 1
  | 8, 1 => 4
  | 8, 2 => 5
  | 8, 3 => 11
  | 9, 0 => 1
  | 9, 1 => 4
  | 9, 2 => 10
  | 9, 3 => 11
  | 10, 0 => 1
  | 10, 1 => 7
  | 10, 2 => 8
  | 10, 3 => 11
  | 11, 0 => 1
  | 11, 1 => 7
  | 11, 2 => 10
  | 11, 3 => 11

/-- Global edge representative for every local tetrahedral edge slot. -/
def localEdgeOf : T → Fin 6 → E
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
  | 6, 0 => 19
  | 6, 1 => 20
  | 6, 2 => 22
  | 6, 3 => 23
  | 6, 4 => 25
  | 6, 5 => 28
  | 7, 0 => 19
  | 7, 1 => 21
  | 7, 2 => 22
  | 7, 3 => 24
  | 7, 4 => 25
  | 7, 5 => 31
  | 8, 0 => 7
  | 8, 1 => 20
  | 8, 2 => 22
  | 8, 3 => 26
  | 8, 4 => 27
  | 8, 5 => 28
  | 9, 0 => 7
  | 9, 1 => 9
  | 9, 2 => 22
  | 9, 3 => 13
  | 9, 4 => 27
  | 9, 5 => 32
  | 10, 0 => 8
  | 10, 1 => 21
  | 10, 2 => 22
  | 10, 3 => 29
  | 10, 4 => 30
  | 10, 5 => 31
  | 11, 0 => 8
  | 11, 1 => 9
  | 11, 2 => 22
  | 11, 3 => 17
  | 11, 4 => 30
  | 11, 5 => 32

def edgeInTet (e : E) (τ : T) : Option (Fin 6) :=
  if e = localEdgeOf τ 0 then some 0 else
  if e = localEdgeOf τ 1 then some 1 else
  if e = localEdgeOf τ 2 then some 2 else
  if e = localEdgeOf τ 3 then some 3 else
  if e = localEdgeOf τ 4 then some 4 else
  if e = localEdgeOf τ 5 then some 5 else
  none

def twoCubeStrip : Triangulation3D where
  nV := 12
  nE := 33
  nT := 12
  edgeVerts := edgeVerts
  tetVerts := tetVerts
  edgeInTet := edgeInTet
  tet := fun _ => FreudenthalCubeTriangulation.freudenthalTet

theorem edgeInTet_iff_localEdgeOf (e : E) (τ : T) (f : Fin 6) :
    edgeInTet e τ = some f ↔ e = localEdgeOf τ f := by
  native_decide +revert

theorem local_sqEdge_eq_global
    (e : E) (τ : T) (f : Fin 6) (h : edgeInTet e τ = some f) :
    FreudenthalCubeTriangulation.freudenthalTet.sqEdge f = globalSqEdge e := by
  have he : e = localEdgeOf τ f := (edgeInTet_iff_localEdgeOf e τ f).1 h
  subst e
  fin_cases τ <;> fin_cases f <;>
    simp [localEdgeOf, FreudenthalCubeTriangulation.freudenthalTet,
      FreudenthalCubeTriangulation.freudenthalTetSqEdges, globalSqEdge]

theorem edgeInTet_vertices
    (e : E) (τ : T) (f : Fin 6) (h : edgeInTet e τ = some f) :
      let ev := edgeVerts e
      let tv := ReggeRigorousFoundation.edgeVertices f
      (tetVerts τ tv.1 = ev.1 ∧ tetVerts τ tv.2 = ev.2) ∨
        (tetVerts τ tv.1 = ev.2 ∧ tetVerts τ tv.2 = ev.1) := by
  have he : e = localEdgeOf τ f := (edgeInTet_iff_localEdgeOf e τ f).1 h
  subst e
  fin_cases τ <;> fin_cases f <;>
    simp [localEdgeOf, edgeVerts, tetVerts,
      ReggeRigorousFoundation.edgeVertices] at h ⊢

theorem localEdge_complete (τ : T) (f : Fin 6) :
    ∃ e : E, edgeInTet e τ = some f := by
  exact ⟨localEdgeOf τ f, (edgeInTet_iff_localEdgeOf (localEdgeOf τ f) τ f).2 rfl⟩

def twoCubeStrip_incidenceConsistent :
    IncidenceConsistent twoCubeStrip where
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
    exact schlaefliTetrahedronClosedForm FreudenthalCubeTriangulation.freudenthalTet

def twoCubeStrip_edgeSlotPartition :
    IncidenceEdgeSlotPartition twoCubeStrip twoCubeStrip_incidenceConsistent where
  localEdgeOf := localEdgeOf
  edgeInTet_iff := by
    intro e τ f
    exact edgeInTet_iff_localEdgeOf e τ f

def twoCubeStrip_edgeSlotBookkeeping :
    IncidenceEdgeSlotBookkeeping twoCubeStrip twoCubeStrip_incidenceConsistent :=
  incidenceEdgeSlotBookkeeping_of_partition
    twoCubeStrip twoCubeStrip_incidenceConsistent twoCubeStrip_edgeSlotPartition

end

end FreudenthalTwoCubeStrip
end Geometry
end IndisputableMonolith

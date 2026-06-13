import Mathlib.Data.Real.Basic
import IndisputableMonolith.Geometry.ReggeRigorousFoundation

/-!
# Finite 3D Regge Triangulations

This module gives the finite incidence scaffold used to lift local
tetrahedral identities to arbitrary 3D Regge triangulations.
-/

namespace IndisputableMonolith
namespace Geometry
namespace ReggeTriangulation3D

open ReggeRigorousFoundation

noncomputable section

/-- A finite 3D Regge triangulation with abstract incidence data and a
nondegenerate squared-edge tuple on every tetrahedron. -/
structure Triangulation3D where
  nV : ℕ
  nE : ℕ
  nT : ℕ
  edgeVerts : Fin nE → Fin nV × Fin nV
  tetVerts : Fin nT → Fin 4 → Fin nV
  edgeInTet : Fin nE → Fin nT → Option (Fin 6)
  tet : Fin nT → NonDegenerateTet

/-- A global edge variation assigns a derivative to each local tetrahedral
edge.  This separated representation avoids prematurely choosing a global
length-coordinate chart. -/
abbrev LocalEdgeVariation (K : Triangulation3D) :=
  Fin K.nT → Fin 6 → ℝ

end

end ReggeTriangulation3D
end Geometry
end IndisputableMonolith

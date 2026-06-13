import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import IndisputableMonolith.Geometry.CayleyMengerPolynomial
import IndisputableMonolith.Geometry.ReggeRigorousFoundation

/-!
# Euclidean Realizations of Tetrahedra

This module connects the abstract six squared-edge coordinates used by
the Cayley-Menger layer to actual points in Euclidean 3-space.
-/

namespace IndisputableMonolith
namespace Geometry
namespace TetrahedronRealization

open CayleyMengerPolynomial
open ReggeRigorousFoundation

noncomputable section

/-- A tetrahedron realized by four points in Euclidean 3-space.  The
`nondegenerate` field is kept as the affine-independence hypothesis that
will later feed the strict dihedral range and positive-volume proofs. -/
structure RealizedTet where
  p : Fin 4 → EuclideanSpace ℝ (Fin 3)
  nondegenerate : AffineIndependent ℝ p

/-- Convert the local tetrahedral edge index to its endpoint vertices. -/
def edgeVertices3 : Fin 6 → Fin 4 × Fin 4 :=
  ReggeRigorousFoundation.edgeVertices

/-- Edge vector from `i` to `j`. -/
def edgeVector (T : RealizedTet) (i j : Fin 4) : EuclideanSpace ℝ (Fin 3) :=
  T.p j - T.p i

/-- Squared length of an edge between two vertices. -/
def vertexSqDist (T : RealizedTet) (i j : Fin 4) : ℝ :=
  ‖edgeVector T i j‖ ^ 2

/-- Extract the six squared edge lengths in the same order as `SqEdges`. -/
def sqEdgeOfPoints (T : RealizedTet) : SqEdges :=
  fun e =>
    let v := edgeVertices3 e
    vertexSqDist T v.1 v.2

/-- Squared edge lengths from points are nonnegative. -/
theorem sqEdgeOfPoints_nonneg (T : RealizedTet) (e : Fin 6) :
    0 ≤ sqEdgeOfPoints T e := by
  unfold sqEdgeOfPoints vertexSqDist
  exact sq_nonneg _

/-- The three edge vectors from vertex `0` that span the tetrahedron. -/
def basisEdgeVector (T : RealizedTet) : Fin 3 → EuclideanSpace ℝ (Fin 3)
  | 0 => edgeVector T 0 1
  | 1 => edgeVector T 0 2
  | 2 => edgeVector T 0 3

/-- Gram matrix of the three edge vectors based at vertex `0`. -/
def gram3 (T : RealizedTet) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => inner ℝ (basisEdgeVector T i) (basisEdgeVector T j)

/-- The Gram matrix is symmetric. -/
theorem gram3_symm (T : RealizedTet) (i j : Fin 3) :
    gram3 T i j = gram3 T j i := by
  unfold gram3
  rw [real_inner_comm]

/-- Euclidean oriented volume squared from the Gram determinant:
`V² = det(Gram) / 36`. -/
def volumeSqFromGram (T : RealizedTet) : ℝ :=
  Matrix.det (gram3 T) / 36

/-- The defining Gram-volume identity. -/
theorem det_gram3_eq_36_volumeSq (T : RealizedTet) :
    Matrix.det (gram3 T) = 36 * volumeSqFromGram T := by
  unfold volumeSqFromGram
  ring

/-- Cayley-Menger volume squared from the extracted edge data:
`V² = cm3 / 288`. -/
def volumeSqFromCM (T : RealizedTet) : ℝ :=
  cm3 (sqEdgeOfPoints T) / 288

/-- The theorem target connecting the Euclidean Gram volume to the
Cayley-Menger volume for realized tetrahedra. -/
def GramCayleyMengerVolumeTheorem : Prop :=
  ∀ T : RealizedTet, volumeSqFromCM T = volumeSqFromGram T

end

end TetrahedronRealization
end Geometry
end IndisputableMonolith

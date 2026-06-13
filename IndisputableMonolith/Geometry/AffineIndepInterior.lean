import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import IndisputableMonolith.Geometry.DihedralCofactorFormula

/-!
# Strict Dihedral Interior from Face-Normal Independence

This module supplies the strict interior step needed by the Regge closure
program.  The analytic core is independent of tetrahedral bookkeeping:
two linearly independent adjacent face normals have normalized dot product
strictly between `-1` and `1`.

The remaining geometric reduction is to prove the adjacent face-normal
independence from the `AffineIndependent` field of `RealizedTet`; this file
keeps that target explicit while removing the previous arccos endpoint
inputs from downstream calculus once normal independence is available.
-/

namespace IndisputableMonolith
namespace Geometry
namespace AffineIndepInterior

open DihedralCofactorFormula
open TetrahedronRealization
open DihedralCayleyMenger

open scoped Matrix

noncomputable section

/-- View a coordinate vector as the Euclidean `ℓ²` vector used by Mathlib's
inner-product API. -/
def toEuclidean3 (u : Fin 3 → ℝ) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm u

theorem inner_toEuclidean3 (u v : Fin 3 → ℝ) :
    inner ℝ (toEuclidean3 u) (toEuclidean3 v) = u ⬝ᵥ v := by
  unfold toEuclidean3
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

theorem norm_toEuclidean3_sq (u : Fin 3 → ℝ) :
    ‖toEuclidean3 u‖ ^ 2 = u ⬝ᵥ u := by
  unfold toEuclidean3
  rw [← real_inner_self_eq_norm_sq]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp

theorem sqrt_dot_self_mul_self_eq_norm_mul_norm (u v : Fin 3 → ℝ) :
    Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v)) =
      ‖toEuclidean3 u‖ * ‖toEuclidean3 v‖ := by
  rw [← norm_toEuclidean3_sq u, ← norm_toEuclidean3_sq v]
  rw [show ‖toEuclidean3 u‖ ^ 2 * ‖toEuclidean3 v‖ ^ 2 =
      (‖toEuclidean3 u‖ * ‖toEuclidean3 v‖) ^ 2 by ring]
  exact Real.sqrt_sq
    (mul_nonneg (norm_nonneg (toEuclidean3 u)) (norm_nonneg (toEuclidean3 v)))

theorem toEuclidean3_smul (r : ℝ) (u : Fin 3 → ℝ) :
    toEuclidean3 (r • u) = r • toEuclidean3 u := by
  unfold toEuclidean3
  simp

theorem smul_of_toEuclidean3_smul {r : ℝ} {u v : Fin 3 → ℝ}
    (h : toEuclidean3 v = r • toEuclidean3 u) : v = r • u := by
  have h' := congrArg (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)) h
  simpa [toEuclidean3] using h'

/-- The normalized dot product of two coordinate vectors is not `1` when
the vectors are linearly independent. -/
theorem dot_div_sqrt_ne_one_of_linearIndependent
    {u v : Fin 3 → ℝ} (hlin : LinearIndependent ℝ ![u, v]) :
    (u ⬝ᵥ v) / Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v)) ≠ 1 := by
  intro h
  have hE :
      inner ℝ (toEuclidean3 u) (toEuclidean3 v) /
        (‖toEuclidean3 u‖ * ‖toEuclidean3 v‖) = 1 := by
    simpa [inner_toEuclidean3, sqrt_dot_self_mul_self_eq_norm_mul_norm] using h
  rcases (real_inner_div_norm_mul_norm_eq_one_iff
      (toEuclidean3 u) (toEuclidean3 v)).1 hE with ⟨huE, r, hr, hvE⟩
  have hu : u ≠ 0 := by
    intro hu0
    apply huE
    unfold toEuclidean3
    simp [hu0]
  have hv : v = r • u := smul_of_toEuclidean3_smul hvE
  exact ((LinearIndependent.pair_iff' hu).1 hlin r) hv.symm

/-- The normalized dot product of two coordinate vectors is not `-1` when
the vectors are linearly independent. -/
theorem dot_div_sqrt_ne_neg_one_of_linearIndependent
    {u v : Fin 3 → ℝ} (hlin : LinearIndependent ℝ ![u, v]) :
    (u ⬝ᵥ v) / Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v)) ≠ -1 := by
  intro h
  have hE :
      inner ℝ (toEuclidean3 u) (toEuclidean3 v) /
        (‖toEuclidean3 u‖ * ‖toEuclidean3 v‖) = -1 := by
    simpa [inner_toEuclidean3, sqrt_dot_self_mul_self_eq_norm_mul_norm] using h
  rcases (real_inner_div_norm_mul_norm_eq_neg_one_iff
      (toEuclidean3 u) (toEuclidean3 v)).1 hE with ⟨huE, r, hr, hvE⟩
  have hu : u ≠ 0 := by
    intro hu0
    apply huE
    unfold toEuclidean3
    simp [hu0]
  have hv : v = r • u := smul_of_toEuclidean3_smul hvE
  exact ((LinearIndependent.pair_iff' hu).1 hlin r) hv.symm

/-- The two adjacent face normals for a tetrahedral edge. -/
def adjacentFaceNormals (T : RealizedTet) (e : Fin 6) :
    (Fin 3 → ℝ) × (Fin 3 → ℝ) :=
  let edge := edgeVertices3 e
  let opp := adjacentFaceOppositeVertices e
  (faceNormal T edge.1 edge.2 opp.1, faceNormal T edge.1 edge.2 opp.2)

/-- Face-normal linear independence is the exact local geometric condition
that excludes the `arccos` endpoint cases. -/
def AdjacentFaceNormalsIndependent (T : RealizedTet) (e : Fin 6) : Prop :=
  LinearIndependent ℝ ![(adjacentFaceNormals T e).1, (adjacentFaceNormals T e).2]

/-- A face normal is nonzero whenever the two edge vectors spanning the face
are linearly independent. -/
theorem faceNormal_ne_zero_of_edgeVectors_linearIndependent
    (T : RealizedTet) (a b c : Fin 4)
    (hlin : LinearIndependent ℝ ![coordEdgeVector T a b, coordEdgeVector T a c]) :
    faceNormal T a b c ≠ 0 := by
  unfold faceNormal
  exact (crossProduct_ne_zero_iff_linearIndependent).2 hlin

/-- Adjacent face-normal independence is equivalent to the cross product of
the two adjacent face normals being nonzero. -/
theorem adjacentFaceNormalsIndependent_iff_cross_ne_zero
    (T : RealizedTet) (e : Fin 6) :
    AdjacentFaceNormalsIndependent T e ↔
      (adjacentFaceNormals T e).1 ⨯₃ (adjacentFaceNormals T e).2 ≠ 0 := by
  unfold AdjacentFaceNormalsIndependent
  exact (crossProduct_ne_zero_iff_linearIndependent).symm

/-- A nonzero cross product of adjacent face normals supplies the strict
interior hypothesis used by the dihedral cosine proof. -/
theorem adjacentFaceNormalsIndependent_of_cross_ne_zero
    (T : RealizedTet) (e : Fin 6)
    (h : (adjacentFaceNormals T e).1 ⨯₃ (adjacentFaceNormals T e).2 ≠ 0) :
    AdjacentFaceNormalsIndependent T e :=
  (adjacentFaceNormalsIndependent_iff_cross_ne_zero T e).2 h

/-- If two face normals share the same edge vector `u`, their cross product
is the scalar triple product times `u`.  This is the algebraic core of the
affine-independence-to-normal-independence step. -/
theorem shared_edge_face_normals_cross
    (u v w : Fin 3 → ℝ) :
    (u ⨯₃ v) ⨯₃ (u ⨯₃ w) = (u ⬝ᵥ v ⨯₃ w) • u := by
  rw [cross_cross_eq_smul_sub_smul']
  have hdot : u ⬝ᵥ (u ⨯₃ v) = 0 := dot_self_cross u v
  rw [hdot, zero_smul, sub_zero]
  rw [show (u ⨯₃ v) ⬝ᵥ w = u ⬝ᵥ v ⨯₃ w by
    rw [dotProduct_comm, triple_product_permutation]]

/-- Adjacent tetrahedral face normals have the shared-edge cross-product
normal form edge-by-edge. -/
theorem adjacentFaceNormals_cross_eq_triple_smul_edge
    (T : RealizedTet) (e : Fin 6) :
    (adjacentFaceNormals T e).1 ⨯₃ (adjacentFaceNormals T e).2 =
      let edge := edgeVertices3 e
      let opp := adjacentFaceOppositeVertices e
      (coordEdgeVector T edge.1 edge.2 ⬝ᵥ
          coordEdgeVector T edge.1 opp.1 ⨯₃ coordEdgeVector T edge.1 opp.2) •
        coordEdgeVector T edge.1 edge.2 := by
  unfold adjacentFaceNormals faceNormal
  dsimp
  exact shared_edge_face_normals_cross _ _ _

/-- Nonzero scalar triple product implies the two face normals adjacent to
the shared edge are linearly independent. -/
theorem faceNormals_independent_of_triple_ne_zero
    {u v w : Fin 3 → ℝ}
    (htriple : u ⬝ᵥ v ⨯₃ w ≠ 0) :
    LinearIndependent ℝ ![u ⨯₃ v, u ⨯₃ w] := by
  have hu : u ≠ 0 := by
    intro hu0
    apply htriple
    simp [hu0]
  have hcross : (u ⨯₃ v) ⨯₃ (u ⨯₃ w) ≠ 0 := by
    rw [shared_edge_face_normals_cross]
    exact smul_ne_zero htriple hu
  exact (crossProduct_ne_zero_iff_linearIndependent).1 hcross

/-- Linear independence of three coordinate vectors forces their scalar
triple product to be nonzero. -/
theorem scalar_triple_ne_zero_of_linearIndependent
    {u v w : Fin 3 → ℝ}
    (hlin : LinearIndependent ℝ ![u, v, w]) :
    u ⬝ᵥ v ⨯₃ w ≠ 0 := by
  have hunit : IsUnit (Matrix.of ![u, v, w]).det := by
    have hrows : LinearIndependent ℝ (Matrix.of ![u, v, w]).row := by
      simpa [Matrix.row] using hlin
    exact (Matrix.isUnit_iff_isUnit_det _).1
      ((Matrix.linearIndependent_rows_iff_isUnit).1 hrows)
  have hdet_ne : Matrix.det ![u, v, w] ≠ 0 := hunit.ne_zero
  simpa [triple_product_eq_det] using hdet_ne

/-- Coordinate extraction through `EuclideanSpace.equiv` preserves linear
independence. -/
theorem coord_linearIndependent_of_euclidean
    {v : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hlin : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun i => (v i).ofLp) := by
  let L := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).toLinearMap
  have hmap : LinearIndependent ℝ (L ∘ v) := by
    exact hlin.map' L (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).toLinearEquiv.ker
  simpa [L, Function.comp_def] using hmap

/-- Edge-local scalar triple product nonvanishing implies adjacent face-normal
independence. -/
theorem adjacentFaceNormalsIndependent_of_triple_ne_zero
    (T : RealizedTet) (e : Fin 6)
    (htriple :
      let edge := edgeVertices3 e
      let opp := adjacentFaceOppositeVertices e
      coordEdgeVector T edge.1 edge.2 ⬝ᵥ
        coordEdgeVector T edge.1 opp.1 ⨯₃ coordEdgeVector T edge.1 opp.2 ≠ 0) :
    AdjacentFaceNormalsIndependent T e := by
  unfold AdjacentFaceNormalsIndependent adjacentFaceNormals faceNormal
  dsimp at htriple ⊢
  exact faceNormals_independent_of_triple_ne_zero htriple

/-- The three base edge vectors of a realized tetrahedron are linearly
independent. -/
theorem basisEdgeVector_linearIndependent (T : RealizedTet) :
    LinearIndependent ℝ (basisEdgeVector T) := by
  have h := T.nondegenerate
  rw [affineIndependent_iff_linearIndependent_vsub ℝ T.p (0 : Fin 4)] at h
  let e : Fin 3 ≃ { j : Fin 4 // j ≠ 0 } := {
    toFun := fun i =>
      match i with
      | 0 => ⟨1, by decide⟩
      | 1 => ⟨2, by decide⟩
      | 2 => ⟨3, by decide⟩
    invFun := fun j =>
      match j with
      | ⟨1, _⟩ => 0
      | ⟨2, _⟩ => 1
      | ⟨3, _⟩ => 2
      | ⟨0, h0⟩ => False.elim (h0 rfl)
    left_inv := by
      intro i
      fin_cases i <;> rfl
    right_inv := by
      intro j
      rcases j with ⟨j, hj⟩
      fin_cases j <;> simp at hj ⊢
  }
  have h' := LinearIndependent.comp h e e.injective
  convert h' using 1
  ext i
  fin_cases i <;> rfl

/-- Coordinate edge vectors from any fixed base vertex to the other three
vertices are linearly independent, for any ordering of those three vertices. -/
theorem coordEdgeVector_from_base_linearIndependent
    (T : RealizedTet) (base : Fin 4)
    (e : Fin 3 ≃ { j : Fin 4 // j ≠ base }) :
    LinearIndependent ℝ (fun i : Fin 3 => coordEdgeVector T base (e i).1) := by
  have h := T.nondegenerate
  rw [affineIndependent_iff_linearIndependent_vsub ℝ T.p base] at h
  have h' := LinearIndependent.comp h e e.injective
  have hcoord := coord_linearIndependent_of_euclidean h'
  exact hcoord

/-- For each tetrahedral edge, the shared edge and the two vectors to the
opposite vertices form a linearly independent coordinate triple. -/
theorem edge_opposite_coord_triple_linearIndependent
    (T : RealizedTet) (e : Fin 6) :
    let edge := edgeVertices3 e
    let opp := adjacentFaceOppositeVertices e
    LinearIndependent ℝ ![
      coordEdgeVector T edge.1 edge.2,
      coordEdgeVector T edge.1 opp.1,
      coordEdgeVector T edge.1 opp.2] := by
  fin_cases e
  · let E : Fin 3 ≃ { j : Fin 4 // j ≠ 0 } := {
      toFun := fun i =>
        match i with
        | 0 => ⟨1, by decide⟩
        | 1 => ⟨2, by decide⟩
        | 2 => ⟨3, by decide⟩
      invFun := fun j =>
        match j with
        | ⟨1, _⟩ => 0
        | ⟨2, _⟩ => 1
        | ⟨3, _⟩ => 2
        | ⟨0, h0⟩ => False.elim (h0 rfl)
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by
        intro j
        rcases j with ⟨j, hj⟩
        fin_cases j <;> simp at hj ⊢
    }
    simp [edgeVertices3, adjacentFaceOppositeVertices,
      ReggeRigorousFoundation.edgeVertices]
    convert coordEdgeVector_from_base_linearIndependent T 0 E using 1
    ext i
    fin_cases i <;> rfl
  · let E : Fin 3 ≃ { j : Fin 4 // j ≠ 0 } := {
      toFun := fun i =>
        match i with
        | 0 => ⟨2, by decide⟩
        | 1 => ⟨1, by decide⟩
        | 2 => ⟨3, by decide⟩
      invFun := fun j =>
        match j with
        | ⟨2, _⟩ => 0
        | ⟨1, _⟩ => 1
        | ⟨3, _⟩ => 2
        | ⟨0, h0⟩ => False.elim (h0 rfl)
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by
        intro j
        rcases j with ⟨j, hj⟩
        fin_cases j <;> simp at hj ⊢
    }
    simp [edgeVertices3, adjacentFaceOppositeVertices,
      ReggeRigorousFoundation.edgeVertices]
    convert coordEdgeVector_from_base_linearIndependent T 0 E using 1
    ext i
    fin_cases i <;> rfl
  · let E : Fin 3 ≃ { j : Fin 4 // j ≠ 0 } := {
      toFun := fun i =>
        match i with
        | 0 => ⟨3, by decide⟩
        | 1 => ⟨1, by decide⟩
        | 2 => ⟨2, by decide⟩
      invFun := fun j =>
        match j with
        | ⟨3, _⟩ => 0
        | ⟨1, _⟩ => 1
        | ⟨2, _⟩ => 2
        | ⟨0, h0⟩ => False.elim (h0 rfl)
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by
        intro j
        rcases j with ⟨j, hj⟩
        fin_cases j <;> simp at hj ⊢
    }
    simp [edgeVertices3, adjacentFaceOppositeVertices,
      ReggeRigorousFoundation.edgeVertices]
    convert coordEdgeVector_from_base_linearIndependent T 0 E using 1
    ext i
    fin_cases i <;> rfl
  · let E : Fin 3 ≃ { j : Fin 4 // j ≠ 1 } := {
      toFun := fun i =>
        match i with
        | 0 => ⟨2, by decide⟩
        | 1 => ⟨0, by decide⟩
        | 2 => ⟨3, by decide⟩
      invFun := fun j =>
        match j with
        | ⟨2, _⟩ => 0
        | ⟨0, _⟩ => 1
        | ⟨3, _⟩ => 2
        | ⟨1, h1⟩ => False.elim (h1 rfl)
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by
        intro j
        rcases j with ⟨j, hj⟩
        fin_cases j <;> simp at hj ⊢
    }
    simp [edgeVertices3, adjacentFaceOppositeVertices,
      ReggeRigorousFoundation.edgeVertices]
    convert coordEdgeVector_from_base_linearIndependent T 1 E using 1
    ext i
    fin_cases i <;> rfl
  · let E : Fin 3 ≃ { j : Fin 4 // j ≠ 1 } := {
      toFun := fun i =>
        match i with
        | 0 => ⟨3, by decide⟩
        | 1 => ⟨0, by decide⟩
        | 2 => ⟨2, by decide⟩
      invFun := fun j =>
        match j with
        | ⟨3, _⟩ => 0
        | ⟨0, _⟩ => 1
        | ⟨2, _⟩ => 2
        | ⟨1, h1⟩ => False.elim (h1 rfl)
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by
        intro j
        rcases j with ⟨j, hj⟩
        fin_cases j <;> simp at hj ⊢
    }
    simp [edgeVertices3, adjacentFaceOppositeVertices,
      ReggeRigorousFoundation.edgeVertices]
    convert coordEdgeVector_from_base_linearIndependent T 1 E using 1
    ext i
    fin_cases i <;> rfl
  · let E : Fin 3 ≃ { j : Fin 4 // j ≠ 2 } := {
      toFun := fun i =>
        match i with
        | 0 => ⟨3, by decide⟩
        | 1 => ⟨0, by decide⟩
        | 2 => ⟨1, by decide⟩
      invFun := fun j =>
        match j with
        | ⟨3, _⟩ => 0
        | ⟨0, _⟩ => 1
        | ⟨1, _⟩ => 2
        | ⟨2, h2⟩ => False.elim (h2 rfl)
      left_inv := by intro i; fin_cases i <;> rfl
      right_inv := by
        intro j
        rcases j with ⟨j, hj⟩
        fin_cases j <;> simp at hj ⊢
    }
    simp [edgeVertices3, adjacentFaceOppositeVertices,
      ReggeRigorousFoundation.edgeVertices]
    convert coordEdgeVector_from_base_linearIndependent T 2 E using 1
    ext i
    fin_cases i <;> rfl

/-- Affine independence of the tetrahedron implies adjacent face-normal
independence for every edge. -/
theorem adjacentFaceNormalsIndependent_of_affineIndependent
    (T : RealizedTet) (e : Fin 6) :
    AdjacentFaceNormalsIndependent T e := by
  have hlin := edge_opposite_coord_triple_linearIndependent T e
  have htriple := scalar_triple_ne_zero_of_linearIndependent hlin
  exact adjacentFaceNormalsIndependent_of_triple_ne_zero T e htriple

/-- Strict interior for the geometric dihedral cosine, given linear
independence of the two adjacent face normals. -/
theorem geometricDihedralCos_strict_interior_of_faceNormals_independent
    (T : RealizedTet) (e : Fin 6)
    (hlin : AdjacentFaceNormalsIndependent T e) :
    -1 < geometricDihedralCos T e ∧ geometricDihedralCos T e < 1 := by
  refine geometricDihedralCos_interior_of_ne_endpoints T e ?_ ?_
  · unfold geometricDihedralCos geometricDihedralNumerator geometricDihedralDenomSq
    unfold AdjacentFaceNormalsIndependent adjacentFaceNormals at hlin
    dsimp at hlin ⊢
    exact dot_div_sqrt_ne_neg_one_of_linearIndependent hlin
  · unfold geometricDihedralCos geometricDihedralNumerator geometricDihedralDenomSq
    unfold AdjacentFaceNormalsIndependent adjacentFaceNormals at hlin
    dsimp at hlin ⊢
    exact dot_div_sqrt_ne_one_of_linearIndependent hlin

/-- Strict interior transferred to the Cayley-Menger cofactor cosine for a
realized tetrahedron. -/
theorem dihedralCos3Sq_strict_interior_of_faceNormals_independent
    (T : RealizedTet) (e : Fin 6)
    (hlin : AdjacentFaceNormalsIndependent T e) :
    -1 < dihedralCos3Sq (sqEdgeOfPoints T) e ∧
      dihedralCos3Sq (sqEdgeOfPoints T) e < 1 := by
  rw [← geometricDihedralCos_eq_cmCofactorRatio T e]
  exact geometricDihedralCos_strict_interior_of_faceNormals_independent T e hlin

/-- Affine independence of the realized tetrahedron gives strict interior for
the geometric dihedral cosine at every edge. -/
theorem geometricDihedralCos_strict_interior_of_affineIndependent
    (T : RealizedTet) (e : Fin 6) :
    -1 < geometricDihedralCos T e ∧ geometricDihedralCos T e < 1 :=
  geometricDihedralCos_strict_interior_of_faceNormals_independent T e
    (adjacentFaceNormalsIndependent_of_affineIndependent T e)

/-- Affine independence of the realized tetrahedron gives strict interior for
the Cayley-Menger cofactor cosine at every edge. -/
theorem dihedralCos3Sq_strict_interior_of_affineIndependent
    (T : RealizedTet) (e : Fin 6) :
    -1 < dihedralCos3Sq (sqEdgeOfPoints T) e ∧
      dihedralCos3Sq (sqEdgeOfPoints T) e < 1 :=
  dihedralCos3Sq_strict_interior_of_faceNormals_independent T e
    (adjacentFaceNormalsIndependent_of_affineIndependent T e)

/-- A realized nondegenerate tetrahedron packages an abstract
`NonDegenerateTet` with a Euclidean realization and the face-normal
independence needed for strict dihedral interior.  The final affine
independence closure target is to build the last field from
`RealizedTet.nondegenerate` alone. -/
structure RealizedNonDegenerateTet where
  tet : ReggeRigorousFoundation.NonDegenerateTet
  realization : RealizedTet
  realizes : sqEdgeOfPoints realization = tet.sqEdge

theorem RealizedNonDegenerateTet.dihedralCos3_strict_interior
    (T : RealizedNonDegenerateTet) (e : Fin 6) :
    -1 < dihedralCos3 T.tet e ∧ dihedralCos3 T.tet e < 1 := by
  unfold dihedralCos3
  rw [← T.realizes]
  exact dihedralCos3Sq_strict_interior_of_affineIndependent T.realization e

/-- Construct angle data from a realized tetrahedron with proved strict
interior, without caller-supplied endpoint or range hypotheses. -/
def RealizedNonDegenerateTet.dihedralAngleData3
    (T : RealizedNonDegenerateTet) (e : Fin 6) :
    DihedralAngle.DihedralAngleData :=
  let h := T.dihedralCos3_strict_interior e
  DihedralCayleyMenger.dihedralAngleData3 T.tet e (le_of_lt h.1) (le_of_lt h.2)

end

end AffineIndepInterior
end Geometry
end IndisputableMonolith

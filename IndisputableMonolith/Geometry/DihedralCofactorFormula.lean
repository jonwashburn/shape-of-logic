import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import IndisputableMonolith.Geometry.GramCayleyMenger
import IndisputableMonolith.Geometry.DihedralCayleyMenger

/-!
# Berger Cofactor Formula Target

This module defines the Euclidean geometric side of the tetrahedral
dihedral cosine: face normals from cross products and the normalized
inner product of the two adjacent face normals.

The remaining theorem in this module is the Berger cofactor formula,
which will identify this geometric cosine with the Cayley-Menger cofactor
ratio in `DihedralCayleyMenger`.
-/

namespace IndisputableMonolith
namespace Geometry
namespace DihedralCofactorFormula

open TetrahedronRealization
open DihedralCayleyMenger
open CayleyMengerPolynomial
open CayleyMengerMatrix

open scoped Matrix

noncomputable section

/-- The two faces adjacent to an edge, represented by the opposite vertices
of those faces.  For edge `(i,j)`, these are the two remaining vertices. -/
def adjacentFaceOppositeVertices : Fin 6 → Fin 4 × Fin 4
  | 0 => (2, 3)
  | 1 => (1, 3)
  | 2 => (1, 2)
  | 3 => (0, 3)
  | 4 => (0, 2)
  | 5 => (0, 1)

/-- Coordinate vector for the edge from `a` to `b`. -/
def coordEdgeVector (T : RealizedTet) (a b : Fin 4) : Fin 3 → ℝ :=
  (T.p b - T.p a).ofLp

/-- Coordinate dot products agree with the real inner product of the
corresponding Euclidean edge vectors. -/
theorem coordEdgeVector_dot_eq_inner
    (T : RealizedTet) (a b c d : Fin 4) :
    coordEdgeVector T a b ⬝ᵥ coordEdgeVector T c d =
      inner ℝ (edgeVector T a b) (edgeVector T c d) := by
  unfold coordEdgeVector edgeVector
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- Rebase any coordinate edge vector at vertex `0`. -/
theorem coordEdgeVector_eq_base_sub (T : RealizedTet) (a b : Fin 4) :
    coordEdgeVector T a b = coordEdgeVector T 0 b - coordEdgeVector T 0 a := by
  unfold coordEdgeVector
  ext k
  simp

/-- Dot product of two coordinate edge vectors after rebasing at vertex `0`. -/
theorem coordEdgeVector_dot_base_sub (T : RealizedTet) (a b c d : Fin 4) :
    coordEdgeVector T a b ⬝ᵥ coordEdgeVector T c d =
      (coordEdgeVector T 0 b - coordEdgeVector T 0 a) ⬝ᵥ
        (coordEdgeVector T 0 d - coordEdgeVector T 0 c) := by
  rw [coordEdgeVector_eq_base_sub T a b, coordEdgeVector_eq_base_sub T c d]

/-- Face normal for the face through vertices `(a,b,c)`, as a coordinate
vector in `ℝ^3`. -/
def faceNormal (T : RealizedTet) (a b c : Fin 4) : Fin 3 → ℝ :=
  coordEdgeVector T a b ⨯₃ coordEdgeVector T a c

/-- Dot product of two face normals, reduced by the cross-dot-cross identity. -/
theorem faceNormal_dot_faceNormal
    (T : RealizedTet) (a b c d e f : Fin 4) :
    faceNormal T a b c ⬝ᵥ faceNormal T d e f =
      (coordEdgeVector T a b ⬝ᵥ coordEdgeVector T d e) *
        (coordEdgeVector T a c ⬝ᵥ coordEdgeVector T d f)
      - (coordEdgeVector T a b ⬝ᵥ coordEdgeVector T d f) *
        (coordEdgeVector T a c ⬝ᵥ coordEdgeVector T d e) := by
  unfold faceNormal
  rw [cross_dot_cross]

/-- Squared norm of a face normal, reduced to edge-vector dot products. -/
theorem faceNormal_dot_self
    (T : RealizedTet) (a b c : Fin 4) :
    faceNormal T a b c ⬝ᵥ faceNormal T a b c =
      (coordEdgeVector T a b ⬝ᵥ coordEdgeVector T a b) *
        (coordEdgeVector T a c ⬝ᵥ coordEdgeVector T a c)
      - (coordEdgeVector T a b ⬝ᵥ coordEdgeVector T a c) *
        (coordEdgeVector T a c ⬝ᵥ coordEdgeVector T a b) := by
  simpa using faceNormal_dot_faceNormal T a b c a b c

/-- The numerator of the geometric dihedral cosine at an edge, before
normalization. -/
def geometricDihedralNumerator (T : RealizedTet) (e : Fin 6) : ℝ :=
  let edge := edgeVertices3 e
  let opp := adjacentFaceOppositeVertices e
  faceNormal T edge.1 edge.2 opp.1 ⬝ᵥ faceNormal T edge.1 edge.2 opp.2

/-- The denominator square of the geometric dihedral cosine at an edge. -/
def geometricDihedralDenomSq (T : RealizedTet) (e : Fin 6) : ℝ :=
  let edge := edgeVertices3 e
  let opp := adjacentFaceOppositeVertices e
  let n₁ := faceNormal T edge.1 edge.2 opp.1
  let n₂ := faceNormal T edge.1 edge.2 opp.2
  (n₁ ⬝ᵥ n₁) * (n₂ ⬝ᵥ n₂)

/-- The internal geometric dihedral cosine at an edge, computed from the
two face normals adjacent to the edge.  The sign is chosen to match the
internal Regge dihedral convention. -/
def geometricDihedralCos (T : RealizedTet) (e : Fin 6) : ℝ :=
  geometricDihedralNumerator T e / Real.sqrt (geometricDihedralDenomSq T e)

/-- Expands the geometric cosine numerator using `cross_dot_cross`. -/
theorem geometricDihedralNumerator_cross
    (T : RealizedTet) (e : Fin 6) :
    geometricDihedralNumerator T e =
      let edge := edgeVertices3 e
      let opp := adjacentFaceOppositeVertices e
      (coordEdgeVector T edge.1 edge.2 ⬝ᵥ coordEdgeVector T edge.1 edge.2) *
        (coordEdgeVector T edge.1 opp.1 ⬝ᵥ coordEdgeVector T edge.1 opp.2)
      - (coordEdgeVector T edge.1 edge.2 ⬝ᵥ coordEdgeVector T edge.1 opp.2) *
        (coordEdgeVector T edge.1 opp.1 ⬝ᵥ coordEdgeVector T edge.1 edge.2) := by
  unfold geometricDihedralNumerator
  dsimp
  rw [faceNormal_dot_faceNormal]

/-- Edge `0 = (0,1)`: the geometric numerator in Gram entries. -/
theorem geometricDihedralNumerator_edge0_gram (T : RealizedTet) :
    geometricDihedralNumerator T 0 =
      gram3 T 0 0 * gram3 T 1 2 - gram3 T 0 2 * gram3 T 1 0 := by
  rw [geometricDihedralNumerator_cross]
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices,
    coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

set_option maxHeartbeats 2000000
/-- Edge `0`: the corresponding Cayley-Menger cofactor equals four times
the geometric numerator. -/
theorem cmCofactor3_edge0_eq_four_geometricNumerator (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 3 4 =
      4 * geometricDihedralNumerator T 0 := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [geometricDihedralNumerator_edge0_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show ¬ Even (7 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 1 0]
  ring

/-- Edge `0`: the first adjacent face-normal square in Gram entries. -/
theorem faceNormal_edge0_left_self_gram (T : RealizedTet) :
    faceNormal T 0 1 2 ⬝ᵥ faceNormal T 0 1 2 =
      gram3 T 0 0 * gram3 T 1 1 - gram3 T 0 1 * gram3 T 1 0 := by
  rw [faceNormal_dot_self]
  simp [coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

/-- Edge `0`: the second adjacent face-normal square in Gram entries. -/
theorem faceNormal_edge0_right_self_gram (T : RealizedTet) :
    faceNormal T 0 1 3 ⬝ᵥ faceNormal T 0 1 3 =
      gram3 T 0 0 * gram3 T 2 2 - gram3 T 0 2 * gram3 T 2 0 := by
  rw [faceNormal_dot_self]
  simp [coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

set_option maxHeartbeats 2000000
/-- Edge `0`: diagonal cofactor for the first adjacent face. -/
theorem cmCofactor3_edge0_left_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 3 3 =
      -4 * (faceNormal T 0 1 3 ⬝ᵥ faceNormal T 0 1 3) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge0_right_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (6 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 2 0]
  ring_nf

set_option maxHeartbeats 2000000
/-- Edge `0`: diagonal cofactor for the second adjacent face. -/
theorem cmCofactor3_edge0_right_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 4 4 =
      -4 * (faceNormal T 0 1 2 ⬝ᵥ faceNormal T 0 1 2) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge0_left_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (8 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 1 0]
  ring_nf

/-- Edge `0`: product of the two diagonal cofactors equals `16` times the
geometric denominator square. -/
theorem cmCofactor3_edge0_diag_product_eq_sixteen_denomSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 3 3 *
      cmCofactor3 (sqEdgeOfPoints T) 4 4 =
        16 * geometricDihedralDenomSq T 0 := by
  rw [cmCofactor3_edge0_left_diag_eq_neg_four_normalSq,
    cmCofactor3_edge0_right_diag_eq_neg_four_normalSq]
  unfold geometricDihedralDenomSq
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  ring

/-- Dot product of a real vector with itself is nonnegative. -/
theorem dotProduct_self_nonneg (v : Fin 3 → ℝ) : 0 ≤ v ⬝ᵥ v := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- The geometric denominator square is nonnegative. -/
theorem geometricDihedralDenomSq_nonneg (T : RealizedTet) (e : Fin 6) :
    0 ≤ geometricDihedralDenomSq T e := by
  unfold geometricDihedralDenomSq
  dsimp
  exact mul_nonneg (dotProduct_self_nonneg _) (dotProduct_self_nonneg _)

/-- Normalized dot products of coordinate vectors lie in `[-1, 1]`. -/
theorem abs_dot_div_sqrt_self_mul_self_le_one (u v : Fin 3 → ℝ) :
    |(u ⬝ᵥ v) / Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v))| ≤ 1 := by
  let U : EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm u
  let V : EuclideanSpace ℝ (Fin 3) := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm v
  have hinner : inner ℝ U V = u ⬝ᵥ v := by
    subst U
    subst V
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct_comm]
  have hUU : ‖U‖ ^ 2 = u ⬝ᵥ u := by
    subst U
    rw [← real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp
  have hVV : ‖V‖ ^ 2 = v ⬝ᵥ v := by
    subst V
    rw [← real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp
  have hsqrt : Real.sqrt ((u ⬝ᵥ u) * (v ⬝ᵥ v)) = ‖U‖ * ‖V‖ := by
    rw [← hUU, ← hVV]
    rw [show ‖U‖ ^ 2 * ‖V‖ ^ 2 = (‖U‖ * ‖V‖) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg (norm_nonneg U) (norm_nonneg V))
  rw [← hinner, hsqrt]
  exact abs_real_inner_div_norm_mul_norm_le_one U V

/-- Geometric dihedral cosines lie in `[-1, 1]`. -/
theorem geometricDihedralCos_range (T : RealizedTet) (e : Fin 6) :
    -1 ≤ geometricDihedralCos T e ∧ geometricDihedralCos T e ≤ 1 := by
  unfold geometricDihedralCos geometricDihedralNumerator geometricDihedralDenomSq
  dsimp
  exact abs_le.mp (abs_dot_div_sqrt_self_mul_self_le_one _ _)

/-- A geometric dihedral cosine is strictly interior once the two endpoint
cases are excluded.  The endpoint-exclusion proof from affine independence is
the remaining geometric step. -/
theorem geometricDihedralCos_interior_of_ne_endpoints
    (T : RealizedTet) (e : Fin 6)
    (hneg : geometricDihedralCos T e ≠ -1)
    (hpos : geometricDihedralCos T e ≠ 1) :
    -1 < geometricDihedralCos T e ∧ geometricDihedralCos T e < 1 := by
  have hr := geometricDihedralCos_range T e
  exact ⟨lt_of_le_of_ne hr.1 (Ne.symm hneg), lt_of_le_of_ne hr.2 hpos⟩

/-- Edge `0`: the diagonal-cofactor square root scales to the geometric
denominator. -/
theorem cmCofactor3_edge0_sqrt_diag_product (T : RealizedTet) :
    Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 3 3 *
        cmCofactor3 (sqEdgeOfPoints T) 4 4)
      = 4 * Real.sqrt (geometricDihedralDenomSq T 0) := by
  rw [cmCofactor3_edge0_diag_product_eq_sixteen_denomSq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [hsqrt16]

/-- Edge `0`: Berger's cofactor formula reduced to the remaining square-root
scaling/positivity fact. -/
theorem geometricDihedralCos_edge0_eq_cofactorRatio_of_sqrt
    (T : RealizedTet)
    (hsqrt :
      Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 3 3 *
        cmCofactor3 (sqEdgeOfPoints T) 4 4)
        = 4 * Real.sqrt (geometricDihedralDenomSq T 0)) :
    geometricDihedralCos T 0 = dihedralCos3Sq (sqEdgeOfPoints T) 0 := by
  unfold geometricDihedralCos dihedralCos3Sq dihedralDenom3
  change geometricDihedralNumerator T 0 / Real.sqrt (geometricDihedralDenomSq T 0) =
    cmCofactor3 (sqEdgeOfPoints T) 3 4 /
      Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 3 3 *
        cmCofactor3 (sqEdgeOfPoints T) 4 4)
  rw [cmCofactor3_edge0_eq_four_geometricNumerator, hsqrt]
  field_simp

/-- Edge `0`: Berger's cofactor formula is fully proved. -/
theorem geometricDihedralCos_edge0_eq_cmCofactorRatio (T : RealizedTet) :
    geometricDihedralCos T 0 = dihedralCos3Sq (sqEdgeOfPoints T) 0 :=
  geometricDihedralCos_edge0_eq_cofactorRatio_of_sqrt T
    (cmCofactor3_edge0_sqrt_diag_product T)

/-! ## Edge 1: `(0,2)` -/

theorem geometricDihedralNumerator_edge1_gram (T : RealizedTet) :
    geometricDihedralNumerator T 1 =
      gram3 T 1 1 * gram3 T 0 2 - gram3 T 1 2 * gram3 T 0 1 := by
  rw [geometricDihedralNumerator_cross]
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices,
    coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge1_eq_four_geometricNumerator (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 2 4 =
      4 * geometricDihedralNumerator T 1 := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [geometricDihedralNumerator_edge1_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (6 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem faceNormal_edge1_left_self_gram (T : RealizedTet) :
    faceNormal T 0 2 1 ⬝ᵥ faceNormal T 0 2 1 =
      gram3 T 1 1 * gram3 T 0 0 - gram3 T 1 0 * gram3 T 0 1 := by
  rw [faceNormal_dot_self]
  simp [coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

theorem faceNormal_edge1_right_self_gram (T : RealizedTet) :
    faceNormal T 0 2 3 ⬝ᵥ faceNormal T 0 2 3 =
      gram3 T 1 1 * gram3 T 2 2 - gram3 T 1 2 * gram3 T 2 1 := by
  rw [faceNormal_dot_self]
  simp [coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge1_left_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 2 2 =
      -4 * (faceNormal T 0 2 3 ⬝ᵥ faceNormal T 0 2 3) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge1_right_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (4 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 2 1]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge1_right_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 4 4 =
      -4 * (faceNormal T 0 2 1 ⬝ᵥ faceNormal T 0 2 1) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge1_left_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (8 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 1 0]
  ring_nf

theorem cmCofactor3_edge1_diag_product_eq_sixteen_denomSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 2 2 *
      cmCofactor3 (sqEdgeOfPoints T) 4 4 =
        16 * geometricDihedralDenomSq T 1 := by
  rw [cmCofactor3_edge1_left_diag_eq_neg_four_normalSq,
    cmCofactor3_edge1_right_diag_eq_neg_four_normalSq]
  unfold geometricDihedralDenomSq
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  ring

theorem cmCofactor3_edge1_sqrt_diag_product (T : RealizedTet) :
    Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 2 2 *
        cmCofactor3 (sqEdgeOfPoints T) 4 4)
      = 4 * Real.sqrt (geometricDihedralDenomSq T 1) := by
  rw [cmCofactor3_edge1_diag_product_eq_sixteen_denomSq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [hsqrt16]

theorem geometricDihedralCos_edge1_eq_cmCofactorRatio (T : RealizedTet) :
    geometricDihedralCos T 1 = dihedralCos3Sq (sqEdgeOfPoints T) 1 := by
  unfold geometricDihedralCos dihedralCos3Sq dihedralDenom3
  change geometricDihedralNumerator T 1 / Real.sqrt (geometricDihedralDenomSq T 1) =
    cmCofactor3 (sqEdgeOfPoints T) 2 4 /
      Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 2 2 *
        cmCofactor3 (sqEdgeOfPoints T) 4 4)
  rw [cmCofactor3_edge1_eq_four_geometricNumerator, cmCofactor3_edge1_sqrt_diag_product]
  field_simp

/-! ## Edge 2: `(0,3)` -/

theorem geometricDihedralNumerator_edge2_gram (T : RealizedTet) :
    geometricDihedralNumerator T 2 =
      gram3 T 2 2 * gram3 T 0 1 - gram3 T 2 1 * gram3 T 0 2 := by
  rw [geometricDihedralNumerator_cross]
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices,
    coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge2_eq_four_geometricNumerator (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 2 3 =
      4 * geometricDihedralNumerator T 2 := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [geometricDihedralNumerator_edge2_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show ¬ Even (5 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 2 1]
  ring_nf

theorem faceNormal_edge2_left_self_gram (T : RealizedTet) :
    faceNormal T 0 3 1 ⬝ᵥ faceNormal T 0 3 1 =
      gram3 T 2 2 * gram3 T 0 0 - gram3 T 2 0 * gram3 T 0 2 := by
  rw [faceNormal_dot_self]
  simp [coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

theorem faceNormal_edge2_right_self_gram (T : RealizedTet) :
    faceNormal T 0 3 2 ⬝ᵥ faceNormal T 0 3 2 =
      gram3 T 2 2 * gram3 T 1 1 - gram3 T 2 1 * gram3 T 1 2 := by
  rw [faceNormal_dot_self]
  simp [coordEdgeVector_dot_eq_inner, gram3, basisEdgeVector, edgeVector]

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge2_left_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 2 2 =
      -4 * (faceNormal T 0 3 2 ⬝ᵥ faceNormal T 0 3 2) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge2_right_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (4 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 2 1]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge2_right_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 3 3 =
      -4 * (faceNormal T 0 3 1 ⬝ᵥ faceNormal T 0 3 1) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge2_left_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (6 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 2 0]
  ring_nf

theorem cmCofactor3_edge2_diag_product_eq_sixteen_denomSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 2 2 *
      cmCofactor3 (sqEdgeOfPoints T) 3 3 =
        16 * geometricDihedralDenomSq T 2 := by
  rw [cmCofactor3_edge2_left_diag_eq_neg_four_normalSq,
    cmCofactor3_edge2_right_diag_eq_neg_four_normalSq]
  unfold geometricDihedralDenomSq
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  ring

theorem cmCofactor3_edge2_sqrt_diag_product (T : RealizedTet) :
    Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 2 2 *
        cmCofactor3 (sqEdgeOfPoints T) 3 3)
      = 4 * Real.sqrt (geometricDihedralDenomSq T 2) := by
  rw [cmCofactor3_edge2_diag_product_eq_sixteen_denomSq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [hsqrt16]

theorem geometricDihedralCos_edge2_eq_cmCofactorRatio (T : RealizedTet) :
    geometricDihedralCos T 2 = dihedralCos3Sq (sqEdgeOfPoints T) 2 := by
  unfold geometricDihedralCos dihedralCos3Sq dihedralDenom3
  change geometricDihedralNumerator T 2 / Real.sqrt (geometricDihedralDenomSq T 2) =
    cmCofactor3 (sqEdgeOfPoints T) 2 3 /
      Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 2 2 *
        cmCofactor3 (sqEdgeOfPoints T) 3 3)
  rw [cmCofactor3_edge2_eq_four_geometricNumerator, cmCofactor3_edge2_sqrt_diag_product]
  field_simp

/-! ## Edge 3: `(1,2)` -/

theorem geometricDihedralNumerator_edge3_gram (T : RealizedTet) :
    geometricDihedralNumerator T 3 =
      gram3 T 0 0 * gram3 T 1 1 - gram3 T 0 0 * gram3 T 1 2
        - gram3 T 1 1 * gram3 T 0 2 - gram3 T 0 1 * gram3 T 0 1
        + gram3 T 0 1 * gram3 T 0 2 + gram3 T 0 1 * gram3 T 1 2 := by
  rw [geometricDihedralNumerator_cross]
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  rw [coordEdgeVector_eq_base_sub T 1 2, coordEdgeVector_eq_base_sub T 1 0,
    coordEdgeVector_eq_base_sub T 1 3]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge3_eq_four_geometricNumerator (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 4 =
      4 * geometricDihedralNumerator T 3 := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [geometricDihedralNumerator_edge3_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show ¬ Even (5 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem faceNormal_edge3_left_self_gram (T : RealizedTet) :
    faceNormal T 1 2 0 ⬝ᵥ faceNormal T 1 2 0 =
      gram3 T 0 0 * gram3 T 1 1 - gram3 T 0 1 * gram3 T 1 0 := by
  rw [faceNormal_dot_self]
  rw [coordEdgeVector_eq_base_sub T 1 2, coordEdgeVector_eq_base_sub T 1 0]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

theorem faceNormal_edge3_right_self_gram (T : RealizedTet) :
    faceNormal T 1 2 3 ⬝ᵥ faceNormal T 1 2 3 =
      (gram3 T 0 0 * gram3 T 1 1 + gram3 T 0 0 * gram3 T 2 2
        - 2 * gram3 T 0 0 * gram3 T 1 2 + gram3 T 1 1 * gram3 T 2 2
        - 2 * gram3 T 1 1 * gram3 T 0 2 - 2 * gram3 T 2 2 * gram3 T 0 1
        - gram3 T 0 1 * gram3 T 0 1 + 2 * gram3 T 0 1 * gram3 T 0 2
        + 2 * gram3 T 0 1 * gram3 T 1 2 - gram3 T 0 2 * gram3 T 0 2
        + 2 * gram3 T 0 2 * gram3 T 1 2 - gram3 T 1 2 * gram3 T 1 2) := by
  rw [faceNormal_dot_self]
  rw [coordEdgeVector_eq_base_sub T 1 2, coordEdgeVector_eq_base_sub T 1 3]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge3_left_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 1 =
      -4 * (faceNormal T 1 2 3 ⬝ᵥ faceNormal T 1 2 3) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge3_right_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (2 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge3_right_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 4 4 =
      -4 * (faceNormal T 1 2 0 ⬝ᵥ faceNormal T 1 2 0) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge3_left_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (8 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 1 0]
  ring_nf

theorem cmCofactor3_edge3_diag_product_eq_sixteen_denomSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 1 *
      cmCofactor3 (sqEdgeOfPoints T) 4 4 =
        16 * geometricDihedralDenomSq T 3 := by
  rw [cmCofactor3_edge3_left_diag_eq_neg_four_normalSq,
    cmCofactor3_edge3_right_diag_eq_neg_four_normalSq]
  unfold geometricDihedralDenomSq
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  ring

theorem cmCofactor3_edge3_sqrt_diag_product (T : RealizedTet) :
    Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 1 1 *
        cmCofactor3 (sqEdgeOfPoints T) 4 4)
      = 4 * Real.sqrt (geometricDihedralDenomSq T 3) := by
  rw [cmCofactor3_edge3_diag_product_eq_sixteen_denomSq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [hsqrt16]

theorem geometricDihedralCos_edge3_eq_cmCofactorRatio (T : RealizedTet) :
    geometricDihedralCos T 3 = dihedralCos3Sq (sqEdgeOfPoints T) 3 := by
  unfold geometricDihedralCos dihedralCos3Sq dihedralDenom3
  change geometricDihedralNumerator T 3 / Real.sqrt (geometricDihedralDenomSq T 3) =
    cmCofactor3 (sqEdgeOfPoints T) 1 4 /
      Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 1 1 *
        cmCofactor3 (sqEdgeOfPoints T) 4 4)
  rw [cmCofactor3_edge3_eq_four_geometricNumerator, cmCofactor3_edge3_sqrt_diag_product]
  field_simp

/-! ## Edge 4: `(1,3)` -/

theorem geometricDihedralNumerator_edge4_gram (T : RealizedTet) :
    geometricDihedralNumerator T 4 =
      gram3 T 0 0 * gram3 T 2 2 - gram3 T 0 0 * gram3 T 1 2
        - gram3 T 2 2 * gram3 T 0 1 + gram3 T 0 1 * gram3 T 0 2
        - gram3 T 0 2 * gram3 T 0 2 + gram3 T 0 2 * gram3 T 1 2 := by
  rw [geometricDihedralNumerator_cross]
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  rw [coordEdgeVector_eq_base_sub T 1 3, coordEdgeVector_eq_base_sub T 1 0,
    coordEdgeVector_eq_base_sub T 1 2]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge4_eq_four_geometricNumerator (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 3 =
      4 * geometricDihedralNumerator T 4 := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [geometricDihedralNumerator_edge4_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (4 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem faceNormal_edge4_left_self_gram (T : RealizedTet) :
    faceNormal T 1 3 0 ⬝ᵥ faceNormal T 1 3 0 =
      gram3 T 0 0 * gram3 T 2 2 - gram3 T 0 2 * gram3 T 2 0 := by
  rw [faceNormal_dot_self]
  rw [coordEdgeVector_eq_base_sub T 1 3, coordEdgeVector_eq_base_sub T 1 0]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

theorem faceNormal_edge4_right_self_gram (T : RealizedTet) :
    faceNormal T 1 3 2 ⬝ᵥ faceNormal T 1 3 2 =
      (gram3 T 0 0 * gram3 T 1 1 + gram3 T 0 0 * gram3 T 2 2
        - 2 * gram3 T 0 0 * gram3 T 1 2 + gram3 T 1 1 * gram3 T 2 2
        - 2 * gram3 T 1 1 * gram3 T 0 2 - 2 * gram3 T 2 2 * gram3 T 0 1
        - gram3 T 0 1 * gram3 T 0 1 + 2 * gram3 T 0 1 * gram3 T 0 2
        + 2 * gram3 T 0 1 * gram3 T 1 2 - gram3 T 0 2 * gram3 T 0 2
        + 2 * gram3 T 0 2 * gram3 T 1 2 - gram3 T 1 2 * gram3 T 1 2) := by
  rw [faceNormal_dot_self]
  rw [coordEdgeVector_eq_base_sub T 1 3, coordEdgeVector_eq_base_sub T 1 2]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge4_left_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 1 =
      -4 * (faceNormal T 1 3 2 ⬝ᵥ faceNormal T 1 3 2) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge4_right_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (2 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge4_right_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 3 3 =
      -4 * (faceNormal T 1 3 0 ⬝ᵥ faceNormal T 1 3 0) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge4_left_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (6 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 2 0]
  ring_nf

theorem cmCofactor3_edge4_diag_product_eq_sixteen_denomSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 1 *
      cmCofactor3 (sqEdgeOfPoints T) 3 3 =
        16 * geometricDihedralDenomSq T 4 := by
  rw [cmCofactor3_edge4_left_diag_eq_neg_four_normalSq,
    cmCofactor3_edge4_right_diag_eq_neg_four_normalSq]
  unfold geometricDihedralDenomSq
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  ring

theorem cmCofactor3_edge4_sqrt_diag_product (T : RealizedTet) :
    Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 1 1 *
        cmCofactor3 (sqEdgeOfPoints T) 3 3)
      = 4 * Real.sqrt (geometricDihedralDenomSq T 4) := by
  rw [cmCofactor3_edge4_diag_product_eq_sixteen_denomSq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [hsqrt16]

theorem geometricDihedralCos_edge4_eq_cmCofactorRatio (T : RealizedTet) :
    geometricDihedralCos T 4 = dihedralCos3Sq (sqEdgeOfPoints T) 4 := by
  unfold geometricDihedralCos dihedralCos3Sq dihedralDenom3
  change geometricDihedralNumerator T 4 / Real.sqrt (geometricDihedralDenomSq T 4) =
    cmCofactor3 (sqEdgeOfPoints T) 1 3 /
      Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 1 1 *
        cmCofactor3 (sqEdgeOfPoints T) 3 3)
  rw [cmCofactor3_edge4_eq_four_geometricNumerator, cmCofactor3_edge4_sqrt_diag_product]
  field_simp

/-! ## Edge 5: `(2,3)` -/

theorem geometricDihedralNumerator_edge5_gram (T : RealizedTet) :
    geometricDihedralNumerator T 5 =
      gram3 T 1 1 * gram3 T 2 2 - gram3 T 1 1 * gram3 T 0 2
        - gram3 T 2 2 * gram3 T 0 1 + gram3 T 0 1 * gram3 T 1 2
        + gram3 T 0 2 * gram3 T 1 2 - gram3 T 1 2 * gram3 T 1 2 := by
  rw [geometricDihedralNumerator_cross]
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  rw [coordEdgeVector_eq_base_sub T 2 3, coordEdgeVector_eq_base_sub T 2 0,
    coordEdgeVector_eq_base_sub T 2 1]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge5_eq_four_geometricNumerator (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 2 =
      4 * geometricDihedralNumerator T 5 := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [geometricDihedralNumerator_edge5_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show ¬ Even (3 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

theorem faceNormal_edge5_left_self_gram (T : RealizedTet) :
    faceNormal T 2 3 0 ⬝ᵥ faceNormal T 2 3 0 =
      gram3 T 1 1 * gram3 T 2 2 - gram3 T 1 2 * gram3 T 2 1 := by
  rw [faceNormal_dot_self]
  rw [coordEdgeVector_eq_base_sub T 2 3, coordEdgeVector_eq_base_sub T 2 0]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

theorem faceNormal_edge5_right_self_gram (T : RealizedTet) :
    faceNormal T 2 3 1 ⬝ᵥ faceNormal T 2 3 1 =
      (gram3 T 0 0 * gram3 T 1 1 + gram3 T 0 0 * gram3 T 2 2
        - 2 * gram3 T 0 0 * gram3 T 1 2 + gram3 T 1 1 * gram3 T 2 2
        - 2 * gram3 T 1 1 * gram3 T 0 2 - 2 * gram3 T 2 2 * gram3 T 0 1
        - gram3 T 0 1 * gram3 T 0 1 + 2 * gram3 T 0 1 * gram3 T 0 2
        + 2 * gram3 T 0 1 * gram3 T 1 2 - gram3 T 0 2 * gram3 T 0 2
        + 2 * gram3 T 0 2 * gram3 T 1 2 - gram3 T 1 2 * gram3 T 1 2) := by
  rw [faceNormal_dot_self]
  rw [coordEdgeVector_eq_base_sub T 2 3, coordEdgeVector_eq_base_sub T 2 1]
  simp [sub_dotProduct, dotProduct_sub, coordEdgeVector_dot_eq_inner,
    gram3, basisEdgeVector, edgeVector]
  repeat rw [← real_inner_self_eq_norm_sq]
  simp [inner_sub_left, inner_sub_right, real_inner_comm]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge5_left_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 1 =
      -4 * (faceNormal T 2 3 1 ⬝ᵥ faceNormal T 2 3 1) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge5_right_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (2 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

set_option maxHeartbeats 2000000
theorem cmCofactor3_edge5_right_diag_eq_neg_four_normalSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 2 2 =
      -4 * (faceNormal T 2 3 0 ⬝ᵥ faceNormal T 2 3 0) := by
  rw [GramCayleyMenger.sqEdgeOfPoints_eq_sqEdgesFromGram]
  rw [faceNormal_edge5_left_self_gram]
  unfold cmCofactor3 cmCofactorSign3 cmMinor3 cmMatrix3 GramCayleyMenger.sqEdgesFromGram
  simp [show Even (4 : Nat) by decide, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.succAbove]
  rw [gram3_symm T 2 1]
  ring_nf

theorem cmCofactor3_edge5_diag_product_eq_sixteen_denomSq (T : RealizedTet) :
    cmCofactor3 (sqEdgeOfPoints T) 1 1 *
      cmCofactor3 (sqEdgeOfPoints T) 2 2 =
        16 * geometricDihedralDenomSq T 5 := by
  rw [cmCofactor3_edge5_left_diag_eq_neg_four_normalSq,
    cmCofactor3_edge5_right_diag_eq_neg_four_normalSq]
  unfold geometricDihedralDenomSq
  simp [edgeVertices3, adjacentFaceOppositeVertices, ReggeRigorousFoundation.edgeVertices]
  ring

theorem cmCofactor3_edge5_sqrt_diag_product (T : RealizedTet) :
    Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 1 1 *
        cmCofactor3 (sqEdgeOfPoints T) 2 2)
      = 4 * Real.sqrt (geometricDihedralDenomSq T 5) := by
  rw [cmCofactor3_edge5_diag_product_eq_sixteen_denomSq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)
  rw [hsqrt16]

theorem geometricDihedralCos_edge5_eq_cmCofactorRatio (T : RealizedTet) :
    geometricDihedralCos T 5 = dihedralCos3Sq (sqEdgeOfPoints T) 5 := by
  unfold geometricDihedralCos dihedralCos3Sq dihedralDenom3
  change geometricDihedralNumerator T 5 / Real.sqrt (geometricDihedralDenomSq T 5) =
    cmCofactor3 (sqEdgeOfPoints T) 1 2 /
      Real.sqrt (cmCofactor3 (sqEdgeOfPoints T) 1 1 *
        cmCofactor3 (sqEdgeOfPoints T) 2 2)
  rw [cmCofactor3_edge5_eq_four_geometricNumerator, cmCofactor3_edge5_sqrt_diag_product]
  field_simp

/-- Berger cofactor formula target for realized tetrahedra. -/
def BergerCofactorFormula3 : Prop :=
  ∀ T : RealizedTet, ∀ e : Fin 6,
    geometricDihedralCos T e = dihedralCos3Sq (sqEdgeOfPoints T) e

/-- Berger's cofactor formula for all six tetrahedral edges. -/
theorem geometricDihedralCos_eq_cmCofactorRatio
    (T : RealizedTet) (e : Fin 6) :
    geometricDihedralCos T e = dihedralCos3Sq (sqEdgeOfPoints T) e := by
  fin_cases e
  · exact geometricDihedralCos_edge0_eq_cmCofactorRatio T
  · exact geometricDihedralCos_edge1_eq_cmCofactorRatio T
  · exact geometricDihedralCos_edge2_eq_cmCofactorRatio T
  · exact geometricDihedralCos_edge3_eq_cmCofactorRatio T
  · exact geometricDihedralCos_edge4_eq_cmCofactorRatio T
  · exact geometricDihedralCos_edge5_eq_cmCofactorRatio T

/-- The theorem target is discharged. -/
theorem bergerCofactorFormula3 : BergerCofactorFormula3 :=
  geometricDihedralCos_eq_cmCofactorRatio

/-- Cofactor-defined dihedral cosines of realized tetrahedra lie in `[-1,1]`. -/
theorem dihedralCos3Sq_sqEdgeOfPoints_range (T : RealizedTet) (e : Fin 6) :
    -1 ≤ dihedralCos3Sq (sqEdgeOfPoints T) e ∧
      dihedralCos3Sq (sqEdgeOfPoints T) e ≤ 1 := by
  rw [← geometricDihedralCos_eq_cmCofactorRatio T e]
  exact geometricDihedralCos_range T e

/-- Cofactor dihedral cosines of realized tetrahedra are strictly interior
once endpoint cases are excluded. -/
theorem dihedralCos3Sq_sqEdgeOfPoints_interior_of_ne_endpoints
    (T : RealizedTet) (e : Fin 6)
    (hneg : dihedralCos3Sq (sqEdgeOfPoints T) e ≠ -1)
    (hpos : dihedralCos3Sq (sqEdgeOfPoints T) e ≠ 1) :
    -1 < dihedralCos3Sq (sqEdgeOfPoints T) e ∧
      dihedralCos3Sq (sqEdgeOfPoints T) e < 1 := by
  rw [← geometricDihedralCos_eq_cmCofactorRatio T e] at hneg hpos ⊢
  exact geometricDihedralCos_interior_of_ne_endpoints T e hneg hpos

/-- Any abstract nondegenerate tetrahedron that is realized by Euclidean
points inherits the cofactor cosine range. -/
theorem dihedralCos3_range_of_realization
    (T : ReggeRigorousFoundation.NonDegenerateTet)
    (R : RealizedTet) (hR : sqEdgeOfPoints R = T.sqEdge) (e : Fin 6) :
    -1 ≤ dihedralCos3 T e ∧ dihedralCos3 T e ≤ 1 := by
  unfold dihedralCos3
  rw [← hR]
  exact dihedralCos3Sq_sqEdgeOfPoints_range R e

/-- Build `DihedralAngleData` for a realized abstract tetrahedron without
caller-supplied range proofs. -/
def dihedralAngleData3_of_realization
    (T : ReggeRigorousFoundation.NonDegenerateTet)
    (R : RealizedTet) (hR : sqEdgeOfPoints R = T.sqEdge) (e : Fin 6) :
    DihedralAngle.DihedralAngleData :=
  let hrange := dihedralCos3_range_of_realization T R hR e
  dihedralAngleData3 T e hrange.1 hrange.2

/-- Realized abstract tetrahedra inherit strict cofactor cosine interior
from endpoint exclusion. -/
theorem dihedralCos3_interior_of_realization_ne_endpoints
    (T : ReggeRigorousFoundation.NonDegenerateTet)
    (R : RealizedTet) (hR : sqEdgeOfPoints R = T.sqEdge) (e : Fin 6)
    (hneg : dihedralCos3 T e ≠ -1)
    (hpos : dihedralCos3 T e ≠ 1) :
    -1 < dihedralCos3 T e ∧ dihedralCos3 T e < 1 := by
  unfold dihedralCos3 at hneg hpos ⊢
  rw [← hR] at hneg hpos ⊢
  exact dihedralCos3Sq_sqEdgeOfPoints_interior_of_ne_endpoints R e hneg hpos

end

end DihedralCofactorFormula
end Geometry
end IndisputableMonolith

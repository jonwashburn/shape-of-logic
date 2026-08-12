import IndisputableMonolith.Gravity.Pillar3Successor.RapidityOverlapKernel

/-!
# Natural tensor-contraction classification

This file proves a finite, basis-level version of the naturality theorem
needed by the Pillar-3 successor.

An attachment which is linear in an inverse-metric matrix and separately
linear in two covector legs has a unique coefficient-matrix presentation:
for each supplied matrix `h`, its value is a bilinear form, hence a matrix.
We therefore package the attachment as a linear coefficient kernel

`K : Matrix4 →ₗ[ℝ] Matrix4`.

The no-background/frame-naturality law is the congruence equation

`K(F h Fᵀ) = F (K h) Fᵀ`

for every invertible frame change.  This is not a syntax restriction which
assumes the desired contraction.  It is an extensional equation on an
arbitrary linear endomorphism of the full 16-dimensional matrix space.

The main theorem proves, using only diagonal coordinate scalings and
elementary shears, that on symmetric inverse metrics every such kernel is a
scalar multiple of the supplied metric.  Consequently every attachment in
the class is a scalar multiple of the ordinary tensor contraction.  The
restriction to symmetric inputs is essential and honest: on arbitrary
matrices the identity and transpose contractions are distinct, while they
coincide on inverse metrics.

This is a THEOREM about the explicitly stated local algebraic class.  It does
not assert that S8, S25, or the dual-edge carrier constructs a member of that
class, and it introduces no physical coframe.

No `sorry`, `admit`, or new axiom.
-/

noncomputable section

set_option maxHeartbeats 4000000

namespace IndisputableMonolith
namespace Gravity
namespace Pillar3SuccessorV4
namespace NaturalTensorContractionClassification

open scoped BigOperators
open Matrix
open Pillar3Successor.RapidityOverlapKernel

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) ℝ
abbrev Covector4 := Fin 4 → ℝ

/-! ## Symmetric inverse metrics and frame transport -/

/-- The algebraic symmetry property of an inverse-metric matrix. -/
def IsSymmetricInverseMetric (h : Matrix4) : Prop :=
  h.transpose = h

/-- Congruence transport preserves inverse-metric symmetry. -/
theorem FrameChange4.inverseMetric_isSymmetric
    (change : FrameChange4) (h : Matrix4)
    (hsymmetric : IsSymmetricInverseMetric h) :
    IsSymmetricInverseMetric (change.inverseMetric h) := by
  unfold IsSymmetricInverseMetric at hsymmetric ⊢
  unfold FrameChange4.inverseMetric
  rw [Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.transpose_transpose]
  rw [hsymmetric]
  simp [Matrix.mul_assoc]

theorem FrameChange4.inverseMetric_add
    (change : FrameChange4) (h k : Matrix4) :
    change.inverseMetric (h + k) =
      change.inverseMetric h + change.inverseMetric k := by
  unfold FrameChange4.inverseMetric
  rw [Matrix.mul_add, Matrix.add_mul]

theorem FrameChange4.inverseMetric_smul
    (change : FrameChange4) (r : ℝ) (h : Matrix4) :
    change.inverseMetric (r • h) =
      r • change.inverseMetric h := by
  unfold FrameChange4.inverseMetric
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ## The honest local natural class -/

/--
A local algebraic metric attachment in coefficient-kernel form.

* `kernel` gives metric linearity.
* `Matrix.toBilin' (kernel h)` gives separate linearity in the two covector
  legs.
* `frame_natural` forbids a fixed background matrix or selected coordinate:
  the only matrix argument available to the kernel is the supplied `h`, and
  the output must commute with every invertible congruence change.

The matrix/bilinear-form equivalence in Mathlib makes this presentation
lossless for the stated class of separately bilinear attachments.
-/
structure NaturalLocalMetricAttachment where
  kernel : Matrix4 →ₗ[ℝ] Matrix4
  frame_natural :
    ∀ (change : FrameChange4) (h : Matrix4),
      kernel (change.inverseMetric h) =
        change.inverseMetric (kernel h)

/-- Scalar evaluation of a natural coefficient kernel on two covector legs. -/
def NaturalLocalMetricAttachment.eval
    (attachment : NaturalLocalMetricAttachment)
    (h : Matrix4) (left right : Covector4) : ℝ :=
  Matrix.toBilin' (attachment.kernel h) left right

theorem matrixToBilin_eq_inverseMetricPairing
    (h : Matrix4) (left right : Covector4) :
    Matrix.toBilin' h left right =
      inverseMetricPairing h left right := by
  rw [Matrix.toBilin'_apply]
  simp only [inverseMetricPairing]
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-! ### The promised three linearities -/

theorem NaturalLocalMetricAttachment.eval_zero_metric
    (attachment : NaturalLocalMetricAttachment)
    (left right : Covector4) :
    attachment.eval 0 left right = 0 := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_add_metric
    (attachment : NaturalLocalMetricAttachment)
    (h k : Matrix4) (left right : Covector4) :
    attachment.eval (h + k) left right =
      attachment.eval h left right +
        attachment.eval k left right := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_smul_metric
    (attachment : NaturalLocalMetricAttachment)
    (r : ℝ) (h : Matrix4) (left right : Covector4) :
    attachment.eval (r • h) left right =
      r * attachment.eval h left right := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_zero_left
    (attachment : NaturalLocalMetricAttachment)
    (h : Matrix4) (right : Covector4) :
    attachment.eval h 0 right = 0 := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_add_left
    (attachment : NaturalLocalMetricAttachment)
    (h : Matrix4) (left₁ left₂ right : Covector4) :
    attachment.eval h (left₁ + left₂) right =
      attachment.eval h left₁ right +
        attachment.eval h left₂ right := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_smul_left
    (attachment : NaturalLocalMetricAttachment)
    (r : ℝ) (h : Matrix4) (left right : Covector4) :
    attachment.eval h (r • left) right =
      r * attachment.eval h left right := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_zero_right
    (attachment : NaturalLocalMetricAttachment)
    (h : Matrix4) (left : Covector4) :
    attachment.eval h left 0 = 0 := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_add_right
    (attachment : NaturalLocalMetricAttachment)
    (h : Matrix4) (left right₁ right₂ : Covector4) :
    attachment.eval h left (right₁ + right₂) =
      attachment.eval h left right₁ +
        attachment.eval h left right₂ := by
  simp [NaturalLocalMetricAttachment.eval]

theorem NaturalLocalMetricAttachment.eval_smul_right
    (attachment : NaturalLocalMetricAttachment)
    (r : ℝ) (h : Matrix4) (left right : Covector4) :
    attachment.eval h left (r • right) =
      r * attachment.eval h left right := by
  simp [NaturalLocalMetricAttachment.eval]

/-- The scalar attachment is frame-natural under the correct dual rules. -/
theorem NaturalLocalMetricAttachment.eval_frameNatural
    (attachment : NaturalLocalMetricAttachment)
    (change : FrameChange4) (h : Matrix4)
    (left right : Covector4) :
    attachment.eval (change.inverseMetric h)
        (change.covector left) (change.covector right) =
      attachment.eval h left right := by
  unfold NaturalLocalMetricAttachment.eval
  rw [attachment.frame_natural,
    matrixToBilin_eq_inverseMetricPairing,
    matrixToBilin_eq_inverseMetricPairing]
  exact inverseMetricPairing_frameChange
    change (attachment.kernel h) left right

/-! ## Explicit coordinate changes used by the classification -/

/-- One standard matrix unit. -/
def matrixUnit (i j : Fin 4) : Matrix4 :=
  Matrix.single i j 1

/-- The symmetric basis generator `Eᵢⱼ + Eⱼᵢ`. -/
def symmetricMatrixUnit (i j : Fin 4) : Matrix4 :=
  matrixUnit i j + matrixUnit j i

/-- Diagonal frame coefficient which doubles coordinate `k`. -/
def doubleCoordinate (k : Fin 4) : Fin 4 → ℝ :=
  fun i => if i = k then 2 else 1

/-- Inverse diagonal coefficient for `doubleCoordinate`. -/
def halfCoordinate (k : Fin 4) : Fin 4 → ℝ :=
  fun i => if i = k then (1 / 2 : ℝ) else 1

/-- An explicit invertible frame which doubles exactly one coordinate. -/
def coordinateScaling (k : Fin 4) : FrameChange4 where
  frame := Matrix.diagonal (doubleCoordinate k)
  inverseFrame := Matrix.diagonal (halfCoordinate k)
  inverse_mul_frame := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i = k <;>
        simp [doubleCoordinate, halfCoordinate, hi]
    · simp [Matrix.diagonal, hij]

theorem coordinateScaling_inverseMetric_apply
    (k : Fin 4) (h : Matrix4) (a b : Fin 4) :
    (coordinateScaling k).inverseMetric h a b =
      doubleCoordinate k a * h a b * doubleCoordinate k b := by
  simp [FrameChange4.inverseMetric, coordinateScaling,
    Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem coordinateScaling_matrixUnit
    (k i j : Fin 4) :
    (coordinateScaling k).inverseMetric (matrixUnit i j) =
      (doubleCoordinate k i * doubleCoordinate k j) •
        matrixUnit i j := by
  ext a b
  rw [coordinateScaling_inverseMetric_apply]
  simp [matrixUnit, Matrix.single, doubleCoordinate]
  split_ifs <;> simp_all

/--
The elementary shear `F_t = I + t Eⱼᵢ` and its explicit inverse
`F_{-t}`.
-/
def coordinateShear
    (i j : Fin 4) (hij : i ≠ j) (t : ℝ) : FrameChange4 where
  frame := Matrix.transvection j i t
  inverseFrame := Matrix.transvection j i (-t)
  inverse_mul_frame := by
    rw [Matrix.transvection_mul_transvection_same j i hij.symm]
    simp

/--
Congruence of a diagonal matrix unit under a shear.  This single formula is
the coefficient relation which ties the diagonal and off-diagonal sectors.
-/
theorem coordinateShear_diagonal
    (i j : Fin 4) (hij : i ≠ j) (t : ℝ) :
    (coordinateShear i j hij t).inverseMetric (matrixUnit i i) =
      matrixUnit i i +
        t • symmetricMatrixUnit i j +
        t ^ 2 • matrixUnit j j := by
  unfold FrameChange4.inverseMetric coordinateShear
  simp only [Matrix.transvection, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_single,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  simp only [matrixUnit, Matrix.single_mul_single_same]
  simp [symmetricMatrixUnit, matrixUnit, Matrix.smul_single, pow_two]
  abel

/-! ## Basis-level classification -/

/-- The diagonal coefficient of an arbitrary natural kernel at coordinate `i`. -/
def NaturalLocalMetricAttachment.diagonalCoefficient
    (attachment : NaturalLocalMetricAttachment) (i : Fin 4) : ℝ :=
  attachment.kernel (matrixUnit i i) i i

/-- The canonical scalar extracted at one basis coordinate. -/
def NaturalLocalMetricAttachment.contractionScalar
    (attachment : NaturalLocalMetricAttachment) : ℝ :=
  attachment.diagonalCoefficient 0

/--
Diagonal scaling naturality kills every output entry of `K(Eᵢᵢ)` except its
`(i,i)` entry.
-/
theorem NaturalLocalMetricAttachment.diagonal_support
    (attachment : NaturalLocalMetricAttachment)
    (i a b : Fin 4)
    (hoff : a ≠ i ∨ b ≠ i) :
    attachment.kernel (matrixUnit i i) a b = 0 := by
  rcases hoff with hai | hbi
  · have hn := congrArg (fun X : Matrix4 => X a b)
      (attachment.frame_natural
        (coordinateScaling a) (matrixUnit i i))
    rw [coordinateScaling_matrixUnit] at hn
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul] at hn
    rw [coordinateScaling_inverseMetric_apply] at hn
    by_cases hba : b = a
    · subst b
      simp [doubleCoordinate, hai.symm] at hn
      linarith
    · simp [doubleCoordinate, hai.symm, hba] at hn
      linarith
  · have hn := congrArg (fun X : Matrix4 => X a b)
      (attachment.frame_natural
        (coordinateScaling b) (matrixUnit i i))
    rw [coordinateScaling_matrixUnit] at hn
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul] at hn
    rw [coordinateScaling_inverseMetric_apply] at hn
    by_cases hab : a = b
    · subst a
      simp [doubleCoordinate, hbi.symm] at hn
      linarith
    · simp [doubleCoordinate, hbi.symm, hab] at hn
      linarith

theorem NaturalLocalMetricAttachment.kernel_diagonal
    (attachment : NaturalLocalMetricAttachment) (i : Fin 4) :
    attachment.kernel (matrixUnit i i) =
      attachment.diagonalCoefficient i • matrixUnit i i := by
  ext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = i
    · subst b
      simp [NaturalLocalMetricAttachment.diagonalCoefficient,
        matrixUnit]
    · rw [attachment.diagonal_support i i b (Or.inr hb)]
      simp [matrixUnit, Matrix.single, Ne.symm hb, Matrix.smul_apply]
  · rw [attachment.diagonal_support i a b (Or.inl ha)]
    simp [matrixUnit, Matrix.single, Ne.symm ha, Matrix.smul_apply]

/-- Naturality under an arbitrary shear, expanded using metric linearity. -/
theorem NaturalLocalMetricAttachment.shear_equation
    (attachment : NaturalLocalMetricAttachment)
    (i j : Fin 4) (hij : i ≠ j) (t : ℝ) :
    attachment.diagonalCoefficient i • matrixUnit i i +
          t • attachment.kernel (symmetricMatrixUnit i j) +
          t ^ 2 • attachment.diagonalCoefficient j • matrixUnit j j =
      attachment.diagonalCoefficient i •
        (matrixUnit i i +
          t • symmetricMatrixUnit i j +
          t ^ 2 • matrixUnit j j) := by
  have hn := attachment.frame_natural
    (coordinateShear i j hij t) (matrixUnit i i)
  rw [coordinateShear_diagonal] at hn
  simp only [map_add, map_smul] at hn
  rw [attachment.kernel_diagonal i,
    attachment.kernel_diagonal j] at hn
  rw [FrameChange4.inverseMetric_smul,
    coordinateShear_diagonal] at hn
  exact hn

/-- The two shears `t = ±1` force all diagonal coefficients to agree. -/
theorem NaturalLocalMetricAttachment.diagonalCoefficient_eq
    (attachment : NaturalLocalMetricAttachment)
    (i j : Fin 4) (hij : i ≠ j) :
    attachment.diagonalCoefficient i =
      attachment.diagonalCoefficient j := by
  have hplus := congrArg (fun X : Matrix4 => X j j)
    (attachment.shear_equation i j hij 1)
  have hminus := congrArg (fun X : Matrix4 => X j j)
    (attachment.shear_equation i j hij (-1))
  simp [matrixUnit, symmetricMatrixUnit, Matrix.single,
    Matrix.smul_apply, hij] at hplus hminus
  linarith

/-- The same shear equation fixes every symmetric off-diagonal generator. -/
theorem NaturalLocalMetricAttachment.kernel_symmetricMatrixUnit_of_ne
    (attachment : NaturalLocalMetricAttachment)
    (i j : Fin 4) (hij : i ≠ j) :
    attachment.kernel (symmetricMatrixUnit i j) =
      attachment.diagonalCoefficient i •
        symmetricMatrixUnit i j := by
  have hplus := attachment.shear_equation i j hij 1
  have hcoeff := attachment.diagonalCoefficient_eq i j hij
  rw [← hcoeff] at hplus
  ext a b
  have hab := congrArg (fun X : Matrix4 => X a b) hplus
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    one_mul, one_pow] at hab
  simp only [Matrix.smul_apply, smul_eq_mul]
  linarith

theorem NaturalLocalMetricAttachment.diagonalCoefficient_eq_scalar
    (attachment : NaturalLocalMetricAttachment) (i : Fin 4) :
    attachment.diagonalCoefficient i =
      attachment.contractionScalar := by
  by_cases hi : i = 0
  · subst i
    rfl
  · exact attachment.diagonalCoefficient_eq i 0 hi

/-- Every symmetric matrix-unit generator is an eigenvector with one scalar. -/
theorem NaturalLocalMetricAttachment.kernel_symmetricMatrixUnit
    (attachment : NaturalLocalMetricAttachment)
    (i j : Fin 4) :
    attachment.kernel (symmetricMatrixUnit i j) =
      attachment.contractionScalar • symmetricMatrixUnit i j := by
  by_cases hij : i = j
  · subst j
    simp only [symmetricMatrixUnit, map_add,
      attachment.kernel_diagonal]
    rw [attachment.diagonalCoefficient_eq_scalar]
    module
  · rw [attachment.kernel_symmetricMatrixUnit_of_ne i j hij,
      attachment.diagonalCoefficient_eq_scalar]

/--
Finite symmetric-basis expansion.  Summing over all ordered pairs produces
each off-diagonal entry twice, hence the factor `1/2`.
-/
theorem symmetricMatrix_expansion
    (h : Matrix4) (hsymmetric : IsSymmetricInverseMetric h) :
    h =
      (1 / 2 : ℝ) •
        (∑ i : Fin 4, ∑ j : Fin 4,
          h i j • symmetricMatrixUnit i j) := by
  ext a b
  have hsab : h b a = h a b := by
    have hx := congrArg (fun X : Matrix4 => X a b) hsymmetric
    simpa [IsSymmetricInverseMetric, Matrix.transpose_apply] using hx
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_four, symmetricMatrixUnit, matrixUnit,
      Matrix.single, Matrix.smul_apply] at hsab ⊢ <;>
    linarith

/--
**THEOREM (load-bearing finite naturality classification).**

Every metric-linear, separately feature-bilinear, frame-natural local
attachment with no background tensor is a scalar multiple of the supplied
inverse metric on the symmetric metric locus.
-/
theorem NaturalLocalMetricAttachment.kernel_eq_scalar_on_symmetric
    (attachment : NaturalLocalMetricAttachment)
    (h : Matrix4) (hsymmetric : IsSymmetricInverseMetric h) :
    attachment.kernel h =
      attachment.contractionScalar • h := by
  rw [symmetricMatrix_expansion h hsymmetric]
  simp only [map_smul, map_sum]
  simp_rw [attachment.kernel_symmetricMatrixUnit]
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/--
Scalar form of the classification: the resulting local scalar is exactly a
constant times the standard tensor contraction.
-/
theorem NaturalLocalMetricAttachment.eval_eq_scalar_contraction
    (attachment : NaturalLocalMetricAttachment)
    (h : Matrix4) (hsymmetric : IsSymmetricInverseMetric h)
    (left right : Covector4) :
    attachment.eval h left right =
      attachment.contractionScalar *
        inverseMetricPairing h left right := by
  rw [NaturalLocalMetricAttachment.eval,
    attachment.kernel_eq_scalar_on_symmetric h hsymmetric]
  simpa [matrixToBilin_eq_inverseMetricPairing] using
    congrArg
      (fun form : LinearMap.BilinForm ℝ Covector4 => form left right)
      (map_smul (Matrix.toBilin' : Matrix4 ≃ₗ[ℝ]
        LinearMap.BilinForm ℝ Covector4)
        attachment.contractionScalar h)

/-! ## Canonical inhabitant and normalization -/

/-- The ordinary tensor contraction is an inhabitant of the natural class. -/
def tensorContractionAttachment : NaturalLocalMetricAttachment where
  kernel := LinearMap.id
  frame_natural := by
    intro change h
    rfl

theorem tensorContractionAttachment_eval
    (h : Matrix4) (left right : Covector4) :
    tensorContractionAttachment.eval h left right =
      inverseMetricPairing h left right := by
  rw [NaturalLocalMetricAttachment.eval,
    matrixToBilin_eq_inverseMetricPairing]
  rfl

theorem minkowskiInverse_isSymmetric :
    IsSymmetricInverseMetric minkowskiInverse := by
  ext μ ν
  by_cases hμν : μ = ν
  · subst ν
    rfl
  · have hνμ : ν ≠ μ := Ne.symm hμν
    simp [Matrix.transpose_apply, minkowskiInverse,
      Matrix.diagonal, hμν, hνμ]

theorem minkowski_rest_contraction :
    inverseMetricPairing minkowskiInverse restCovector restCovector = -1 := by
  simp [inverseMetricPairing, minkowskiInverse, restCovector]

/--
Flat normalization fixes the remaining scalar.  This is a normalization
theorem inside the natural class, not a proof that Recognition operations
supply class membership.
-/
theorem NaturalLocalMetricAttachment.flatNormalization_forces_scalar_one
    (attachment : NaturalLocalMetricAttachment)
    (hnormalized :
      attachment.eval minkowskiInverse restCovector restCovector = -1) :
    attachment.contractionScalar = 1 := by
  have hclass := attachment.eval_eq_scalar_contraction
    minkowskiInverse minkowskiInverse_isSymmetric
    restCovector restCovector
  rw [minkowski_rest_contraction] at hclass
  rw [hnormalized] at hclass
  linarith

/--
Two normalized natural attachments agree on every symmetric inverse metric
and every pair of feature covectors.
-/
theorem normalized_natural_attachments_unique
    (leftAttachment rightAttachment : NaturalLocalMetricAttachment)
    (hleft :
      leftAttachment.eval minkowskiInverse
        restCovector restCovector = -1)
    (hright :
      rightAttachment.eval minkowskiInverse
        restCovector restCovector = -1)
    (h : Matrix4) (hsymmetric : IsSymmetricInverseMetric h)
    (left right : Covector4) :
    leftAttachment.eval h left right =
      rightAttachment.eval h left right := by
  rw [leftAttachment.eval_eq_scalar_contraction h hsymmetric,
    rightAttachment.eval_eq_scalar_contraction h hsymmetric,
    leftAttachment.flatNormalization_forces_scalar_one hleft,
    rightAttachment.flatNormalization_forces_scalar_one hright]

/-!
## Typed physical residual

The theorem above closes the mathematical uniqueness question *conditional
on class membership*.  No imported S8/S25 declaration proves that its scalar
event operation constructs independently transforming covector legs or a
linear, congruence-natural map from a variable inverse metric.  Supplying
such a `NaturalLocalMetricAttachment` from the actual Recognition operation
therefore remains a separate physical covariantization premise.
-/

end NaturalTensorContractionClassification
end Pillar3SuccessorV4
end Gravity
end IndisputableMonolith

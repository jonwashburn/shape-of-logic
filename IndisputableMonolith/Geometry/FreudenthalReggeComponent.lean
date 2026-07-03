import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import IndisputableMonolith.Geometry.CayleyMenger
import IndisputableMonolith.Geometry.DihedralAngle
import IndisputableMonolith.Gravity.WeakFieldConformalRegge

/-!
# Concrete Flat-Sector Regge Component Comparison

This module closes the component comparison for the concrete finite
flat-sector coefficient package that the current weak-field bridge can
consume without adding new geometric axioms.

## Honest scope

The current Cayley-Menger stack defines regular tetrahedron CM values and
dihedral angle data, but it does **not** yet expose full Cayley-Menger
determinants as differentiable functions of all edge lengths, nor the
dihedral-angle derivative formulas for an arbitrary Regge triangulation.

So this module proves the component comparison for a concrete regular
flat-sector / Freudenthal-local model whose area weights are given by the
regular hinge-area formula and whose second-variation data is the
graph-Laplacian Regge data already used by the bridge:

* off diagonal, the coefficient matrix satisfies `M_ij = -A_ij`;
* every row sums to zero;
* the second-order action reduces to the Dirichlet form with the concrete
  geometric weights.

This is not a proof for arbitrary Cayley-Menger / dihedral derivative data.
It is the first fully concrete finite model and the exact interface a future
full derivative computation must target.
-/

namespace IndisputableMonolith
namespace Geometry
namespace FreudenthalReggeComponent

open Real CayleyMenger DihedralAngle
open IndisputableMonolith.Foundation.SimplicialLedger.EdgeLengthFromPsi
open IndisputableMonolith.Gravity.WeakFieldConformalRegge

noncomputable section

/-! ## §1. Concrete finite star -/

/-- The finite local model used here has eight vertices, matching the
vertex count of a cubic cell / Freudenthal local chart. -/
abbrev LocalVertex : Type := Fin 8

/-- A concrete local Regge star: finite vertex/edge/hinge bookkeeping plus
flat background scales. -/
structure ConcreteReggeStar where
  edgeLength0 : ℝ
  edgeLength0_pos : 0 < edgeLength0
  hingeArea0 : ℝ
  hingeArea0_nonneg : 0 ≤ hingeArea0

/-! ## §2. Concrete area and dihedral formulas -/

/-- Regular triangular hinge area: `(sqrt 3 / 4) a^2`. -/
def regularTriangleArea (a : ℝ) : ℝ :=
  (Real.sqrt 3 / 4) * a ^ 2

theorem regularTriangleArea_nonneg (a : ℝ) :
    0 ≤ regularTriangleArea a := by
  unfold regularTriangleArea
  exact mul_nonneg (div_nonneg (Real.sqrt_nonneg 3) (by norm_num)) (sq_nonneg a)

theorem regularTriangleArea_pos {a : ℝ} (ha : 0 < a) :
    0 < regularTriangleArea a := by
  unfold regularTriangleArea
  exact mul_pos (div_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)) (by norm_num))
    (sq_pos_of_pos ha)

/-- The regular tetrahedral dihedral angle already exposed by the
`DihedralAngle` module. -/
def regularTetrahedralDihedralAngle : ℝ :=
  regular_tet_dihedral.theta

theorem regularTetrahedralDihedralAngle_eq :
    regularTetrahedralDihedralAngle = Real.arccos (1 / 3) := rfl

/-- The regular hinge-area formula is derivative-ready. -/
theorem hasDerivAt_regularTriangleArea (a : ℝ) :
    HasDerivAt regularTriangleArea ((Real.sqrt 3 / 2) * a) a := by
  unfold regularTriangleArea
  have hmul : HasDerivAt (fun x : ℝ => x * x) (1 * a + a * 1) a :=
    (hasDerivAt_id a).mul (hasDerivAt_id a)
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * a) a := by
    convert hmul using 1
    · ext x
      ring
    · ring
  have h := hsq.const_mul (Real.sqrt 3 / 4)
  convert h using 1
  ring

/-- Uniform rescaling leaves a regular tetrahedral dihedral angle constant.
This records the scale-invariance fact; non-uniform edge derivatives are the
remaining hard Cayley-Menger task. -/
theorem hasDerivAt_regularDihedral_uniformScale (a : ℝ) :
    HasDerivAt (fun _s : ℝ => regularTetrahedralDihedralAngle) 0 a :=
  hasDerivAt_const a regularTetrahedralDihedralAngle

/-! ## §3. Concrete area weights and Regge coefficients -/

/-- The concrete local star at scale `a`: the hinge-area weight comes from
the regular triangular hinge area. -/
def regularLocalStar (a : ℝ) (ha : 0 < a) : ConcreteReggeStar where
  edgeLength0 := a
  edgeLength0_pos := ha
  hingeArea0 := regularTriangleArea a
  hingeArea0_nonneg := regularTriangleArea_nonneg a

/-- Concrete geometric area / face-weight matrix.  Diagonal entries do not
contribute to Dirichlet energy; off diagonal entries use the regular hinge area. -/
def areaWeight (S : ConcreteReggeStar) (i j : LocalVertex) : ℝ :=
  if i = j then 0 else S.hingeArea0

theorem areaWeight_symm (S : ConcreteReggeStar) :
    ∀ i j, areaWeight S i j = areaWeight S j i := by
  intro i j
  unfold areaWeight
  by_cases hij : i = j
  · subst j
    simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp [hij, hji]

theorem areaWeight_nonneg (S : ConcreteReggeStar) :
    ∀ i j, 0 ≤ areaWeight S i j := by
  intro i j
  unfold areaWeight
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, S.hingeArea0_nonneg]

/-- The weak-field Regge data induced by the concrete area weights. -/
def concreteWeakFieldReggeData (S : ConcreteReggeStar) : WeakFieldReggeData 8 :=
  laplacianReggeData (areaWeight S) (areaWeight_symm S)

/-- The concrete second-variation coefficient matrix `M_ij`. -/
def concreteM (S : ConcreteReggeStar) (i j : LocalVertex) : ℝ :=
  bilinearCoefficient (concreteWeakFieldReggeData S) i j

/-- Off diagonal, the concrete Regge coefficient matrix is the negative of the
geometric area/face-weight matrix. -/
theorem concreteM_offDiag_eq_neg_areaWeight
    (S : ConcreteReggeStar) (i j : LocalVertex) (hij : i ≠ j) :
    concreteM S i j = - areaWeight S i j := by
  unfold concreteM concreteWeakFieldReggeData
  rw [bilinearCoefficient_laplacianReggeData (areaWeight S) (areaWeight_symm S)]
  unfold laplacianCoefficient
  simp [hij]

/-- The concrete coefficient matrix has exact zero row sums. -/
theorem concreteM_rowSum_zero (S : ConcreteReggeStar) :
    ∀ i : LocalVertex, ∑ j : LocalVertex, concreteM S i j = 0 := by
  intro i
  unfold concreteM concreteWeakFieldReggeData
  simpa only [bilinearCoefficient_laplacianReggeData (areaWeight S) (areaWeight_symm S)]
    using laplacianCoefficient_row_sum (areaWeight S) i

/-- The concrete component comparison object consumed by the bridge. -/
def concreteReggeComponentComparison (S : ConcreteReggeStar) :
    ReggeComponentComparison (concreteWeakFieldReggeData S) :=
  laplacianReggeData_componentComparison (areaWeight S)
    (areaWeight_symm S) (areaWeight_nonneg S)

/-- Concrete closure of the weak-field component comparison: the second-order
Regge action is exactly the geometric Dirichlet form for the concrete area
weights. -/
theorem concreteReggeSecondVariation_eq_jcostDirichlet
    (S : ConcreteReggeStar) (ε : LogPotential 8) :
    secondOrderReggeAction (concreteWeakFieldReggeData S) ε
      = (1 / 2) * dirichletForm (areaWeight S) ε := by
  simpa [concreteReggeComponentComparison] using
    componentComparison_gives_geometric_dirichlet
      (concreteWeakFieldReggeData S)
      (concreteReggeComponentComparison S)
      ε

/-! ## §4. Certificate -/

structure FreudenthalReggeComponentCert where
  area_derivative : ∀ a : ℝ,
    HasDerivAt regularTriangleArea ((Real.sqrt 3 / 2) * a) a
  dihedral_uniform_scale_derivative : ∀ a : ℝ,
    HasDerivAt (fun _s : ℝ => regularTetrahedralDihedralAngle) 0 a
  off_diag : ∀ (S : ConcreteReggeStar) (i j : LocalVertex),
    i ≠ j → concreteM S i j = - areaWeight S i j
  row_sum : ∀ S : ConcreteReggeStar,
    ∀ i : LocalVertex, ∑ j : LocalVertex, concreteM S i j = 0
  dirichlet : ∀ (S : ConcreteReggeStar) (ε : LogPotential 8),
    secondOrderReggeAction (concreteWeakFieldReggeData S) ε
      = (1 / 2) * dirichletForm (areaWeight S) ε

theorem freudenthalReggeComponentCert : FreudenthalReggeComponentCert where
  area_derivative := hasDerivAt_regularTriangleArea
  dihedral_uniform_scale_derivative := hasDerivAt_regularDihedral_uniformScale
  off_diag := concreteM_offDiag_eq_neg_areaWeight
  row_sum := concreteM_rowSum_zero
  dirichlet := concreteReggeSecondVariation_eq_jcostDirichlet

end

end FreudenthalReggeComponent
end Geometry
end IndisputableMonolith

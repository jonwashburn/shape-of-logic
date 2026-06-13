import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Instances.Matrix
import IndisputableMonolith.Geometry.CayleyMengerPolynomial

/-!
# Cayley-Menger Matrix, Minors, and Cofactors for a Tetrahedron

This module connects the explicit tetrahedral Cayley-Menger polynomial
`cm3` to the actual `5 × 5` Cayley-Menger determinant.  It is the
determinant/cofactor layer needed by the dihedral cosine formula.

The row/column convention is:

```
    0  1  2  3  4
0 [ 0, 1, 1, 1, 1 ]
1 [ 1, 0, a0,a1,a2]
2 [ 1, a0,0, a3,a4]
3 [ 1, a1,a3,0, a5]
4 [ 1, a2,a4,a5,0 ]
```

where `a0..a5` are the squared edge lengths
`(01),(02),(03),(12),(13),(23)`.
-/

namespace IndisputableMonolith
namespace Geometry
namespace CayleyMengerMatrix

open CayleyMengerPolynomial

noncomputable section

/-- The `5 × 5` Cayley-Menger matrix of a tetrahedron, as a function of
the six squared edge lengths. -/
def cmMatrix3 (a : SqEdges) (i j : Fin 5) : ℝ :=
  match i.val, j.val with
  | 0, 0 => 0
  | 0, _ => 1
  | _, 0 => 1
  | 1, 1 => 0
  | 1, 2 => a 0
  | 2, 1 => a 0
  | 1, 3 => a 1
  | 3, 1 => a 1
  | 1, 4 => a 2
  | 4, 1 => a 2
  | 2, 2 => 0
  | 2, 3 => a 3
  | 3, 2 => a 3
  | 2, 4 => a 4
  | 4, 2 => a 4
  | 3, 3 => 0
  | 3, 4 => a 5
  | 4, 3 => a 5
  | 4, 4 => 0
  | _, _ => 0

/-- The Cayley-Menger determinant, computed by Mathlib's matrix determinant. -/
def cmDet3 (a : SqEdges) : ℝ :=
  Matrix.det (cmMatrix3 a)

/-- Delete row `r` and column `c` from the Cayley-Menger matrix and take
the determinant. -/
def cmMinor3 (a : SqEdges) (r c : Fin 5) : ℝ :=
  Matrix.det (Matrix.submatrix (cmMatrix3 a) (Fin.succAbove r) (Fin.succAbove c))

/-- Cofactor sign `(-1)^(r+c)` as a real number. -/
def cmCofactorSign3 (r c : Fin 5) : ℝ :=
  if Even (r.val + c.val) then 1 else -1

/-- Cayley-Menger cofactor `C_{r,c}`. -/
def cmCofactor3 (a : SqEdges) (r c : Fin 5) : ℝ :=
  cmCofactorSign3 r c * cmMinor3 a r c

/-- The Cayley-Menger matrix is symmetric. -/
theorem cmMatrix3_symm (a : SqEdges) (i j : Fin 5) :
    cmMatrix3 a i j = cmMatrix3 a j i := by
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 2000000
/-- Mathlib's determinant of the Cayley-Menger matrix equals the explicit
polynomial `cm3`. -/
theorem cmDet3_eq_cm3 (a : SqEdges) : cmDet3 a = cm3 a := by
  unfold cmDet3 cmMatrix3 cm3
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

/-- Regular unit tetrahedron determinant check. -/
theorem cmDet3_regular_unit : cmDet3 regularUnitSqEdges = 4 := by
  rw [cmDet3_eq_cm3, cm3_regular_unit]

/-- Right-angle unit tetrahedron determinant check. -/
theorem cmDet3_rightAngle_unit : cmDet3 rightAngleUnitSqEdges = 8 := by
  rw [cmDet3_eq_cm3, cm3_rightAngle_unit]

/-- The determinant inherits the smoothness of the explicit polynomial. -/
theorem cmDet3_contDiff (n : ℕ∞) : ContDiff ℝ n cmDet3 := by
  have h : cmDet3 = cm3 := by
    funext a
    exact cmDet3_eq_cm3 a
  rw [h]
  exact cm3_contDiff n

/-- Every entry of the Cayley-Menger matrix is a smooth function of the
six squared edge lengths. -/
theorem cmMatrix3_entry_contDiff (n : ℕ∞) (i j : Fin 5) :
    ContDiff ℝ n (fun a : SqEdges => cmMatrix3 a i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [cmMatrix3] <;> fun_prop

set_option maxHeartbeats 2000000
/-- Every Cayley-Menger minor is a smooth function of the six squared edge
lengths. -/
theorem cmMinor3_contDiff (n : ℕ∞) (r c : Fin 5) :
    ContDiff ℝ n (fun a : SqEdges => cmMinor3 a r c) := by
  unfold cmMinor3 cmMatrix3
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove] <;>
    fun_prop

/-- Every Cayley-Menger cofactor is smooth. -/
theorem cmCofactor3_contDiff (n : ℕ∞) (r c : Fin 5) :
    ContDiff ℝ n (fun a : SqEdges => cmCofactor3 a r c) := by
  unfold cmCofactor3
  exact ContDiff.mul contDiff_const (cmMinor3_contDiff n r c)

/-! ## Regular-unit cofactor normalization

Directly normalizing `Matrix.submatrix` in downstream files produces huge
`Fin.succAbove` goals.  The following explicit determinant lemmas are the
normal forms needed by the regular-tetrahedron cofactor check. -/

/-- The diagonal vertex minor of the regular unit Cayley-Menger matrix. -/
def regularUnitDiagMinorMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 0]

/-- The off-diagonal vertex minor of the regular unit Cayley-Menger matrix. -/
def regularUnitOffDiagMinorMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 1]

def regularUnitOffDiagMinorMatrix24 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 1, 0;
     1, 1, 1, 1]

def regularUnitOffDiagMinorMatrix23 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 0, 1, 1;
     1, 1, 1, 1;
     1, 1, 1, 0]

def regularUnitOffDiagMinorMatrix14 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 0;
     1, 1, 1, 1]

def regularUnitOffDiagMinorMatrix13 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 1;
     1, 1, 1, 0]

def regularUnitOffDiagMinorMatrix12 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![(0 : ℝ), 1, 1, 1;
     1, 1, 1, 1;
     1, 1, 0, 1;
     1, 1, 1, 0]

theorem det_regularUnitDiagMinorMatrix :
    Matrix.det regularUnitDiagMinorMatrix = -3 := by
  unfold regularUnitDiagMinorMatrix
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  norm_num

theorem det_regularUnitOffDiagMinorMatrix :
    Matrix.det regularUnitOffDiagMinorMatrix = -1 := by
  unfold regularUnitOffDiagMinorMatrix
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  norm_num

theorem det_regularUnitOffDiagMinorMatrix24 :
    Matrix.det regularUnitOffDiagMinorMatrix24 = 1 := by
  unfold regularUnitOffDiagMinorMatrix24
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]

theorem det_regularUnitOffDiagMinorMatrix23 :
    Matrix.det regularUnitOffDiagMinorMatrix23 = -1 := by
  unfold regularUnitOffDiagMinorMatrix23
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]

theorem det_regularUnitOffDiagMinorMatrix14 :
    Matrix.det regularUnitOffDiagMinorMatrix14 = -1 := by
  unfold regularUnitOffDiagMinorMatrix14
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]

theorem det_regularUnitOffDiagMinorMatrix13 :
    Matrix.det regularUnitOffDiagMinorMatrix13 = 1 := by
  unfold regularUnitOffDiagMinorMatrix13
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]

theorem det_regularUnitOffDiagMinorMatrix12 :
    Matrix.det regularUnitOffDiagMinorMatrix12 = -1 := by
  unfold regularUnitOffDiagMinorMatrix12
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]

/-- The `(3,4)` regular unit minor reduces to the explicit off-diagonal
normal-form matrix. -/
theorem regularUnit_minor_34_eq_offDiag :
    Matrix.submatrix (cmMatrix3 regularUnitSqEdges) (Fin.succAbove (3 : Fin 5))
      (Fin.succAbove (4 : Fin 5)) = regularUnitOffDiagMinorMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitOffDiagMinorMatrix, cmMatrix3, regularUnitSqEdges, Fin.succAbove]

/-- First off-diagonal regular unit cofactor. -/
theorem regularUnit_cofactor_34 :
    cmCofactor3 regularUnitSqEdges 3 4 = 1 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show ¬ Even (7 : Nat) by decide]
  rw [regularUnit_minor_34_eq_offDiag, det_regularUnitOffDiagMinorMatrix]
  norm_num

theorem regularUnit_minor_24_eq_offDiag :
    Matrix.submatrix (cmMatrix3 regularUnitSqEdges) (Fin.succAbove (2 : Fin 5))
      (Fin.succAbove (4 : Fin 5)) = regularUnitOffDiagMinorMatrix24 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitOffDiagMinorMatrix24, cmMatrix3, regularUnitSqEdges, Fin.succAbove]

theorem regularUnit_cofactor_24 :
    cmCofactor3 regularUnitSqEdges 2 4 = 1 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show Even (6 : Nat) by decide]
  rw [regularUnit_minor_24_eq_offDiag, det_regularUnitOffDiagMinorMatrix24]

theorem regularUnit_minor_23_eq_offDiag :
    Matrix.submatrix (cmMatrix3 regularUnitSqEdges) (Fin.succAbove (2 : Fin 5))
      (Fin.succAbove (3 : Fin 5)) = regularUnitOffDiagMinorMatrix23 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitOffDiagMinorMatrix23, cmMatrix3, regularUnitSqEdges, Fin.succAbove]

theorem regularUnit_cofactor_23 :
    cmCofactor3 regularUnitSqEdges 2 3 = 1 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show ¬ Even (5 : Nat) by decide]
  rw [regularUnit_minor_23_eq_offDiag, det_regularUnitOffDiagMinorMatrix23]
  norm_num

theorem regularUnit_minor_14_eq_offDiag :
    Matrix.submatrix (cmMatrix3 regularUnitSqEdges) (Fin.succAbove (1 : Fin 5))
      (Fin.succAbove (4 : Fin 5)) = regularUnitOffDiagMinorMatrix14 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitOffDiagMinorMatrix14, cmMatrix3, regularUnitSqEdges, Fin.succAbove]

theorem regularUnit_cofactor_14 :
    cmCofactor3 regularUnitSqEdges 1 4 = 1 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show ¬ Even (5 : Nat) by decide]
  rw [regularUnit_minor_14_eq_offDiag, det_regularUnitOffDiagMinorMatrix14]
  norm_num

theorem regularUnit_minor_13_eq_offDiag :
    Matrix.submatrix (cmMatrix3 regularUnitSqEdges) (Fin.succAbove (1 : Fin 5))
      (Fin.succAbove (3 : Fin 5)) = regularUnitOffDiagMinorMatrix13 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitOffDiagMinorMatrix13, cmMatrix3, regularUnitSqEdges, Fin.succAbove]

theorem regularUnit_cofactor_13 :
    cmCofactor3 regularUnitSqEdges 1 3 = 1 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show Even (4 : Nat) by decide]
  rw [regularUnit_minor_13_eq_offDiag, det_regularUnitOffDiagMinorMatrix13]

theorem regularUnit_minor_12_eq_offDiag :
    Matrix.submatrix (cmMatrix3 regularUnitSqEdges) (Fin.succAbove (1 : Fin 5))
      (Fin.succAbove (2 : Fin 5)) = regularUnitOffDiagMinorMatrix12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [regularUnitOffDiagMinorMatrix12, cmMatrix3, regularUnitSqEdges, Fin.succAbove]

theorem regularUnit_cofactor_12 :
    cmCofactor3 regularUnitSqEdges 1 2 = 1 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  simp [show ¬ Even (3 : Nat) by decide]
  rw [regularUnit_minor_12_eq_offDiag, det_regularUnitOffDiagMinorMatrix12]
  norm_num

/-- Any nonzero diagonal vertex minor of the regular unit Cayley-Menger
matrix reduces to the diagonal normal form. -/
theorem regularUnit_diag_minor_eq_normalForm (p : Fin 5) (hp : p ≠ 0) :
    Matrix.submatrix (cmMatrix3 regularUnitSqEdges) (Fin.succAbove p) (Fin.succAbove p)
      = regularUnitDiagMinorMatrix := by
  fin_cases p
  · contradiction
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [regularUnitDiagMinorMatrix, cmMatrix3, regularUnitSqEdges, Fin.succAbove]

/-- Diagonal vertex cofactors of the regular unit tetrahedron. -/
theorem regularUnit_vertex_diag_cofactor (p : Fin 5) (hp : p ≠ 0) :
    cmCofactor3 regularUnitSqEdges p p = -3 := by
  unfold cmCofactor3 cmCofactorSign3 cmMinor3
  have heven : Even (p.val + p.val) := by
    use p.val
  simp [heven]
  rw [regularUnit_diag_minor_eq_normalForm p hp, det_regularUnitDiagMinorMatrix]

/-- The determinant inherits the cubic scaling law from `cm3`. -/
theorem cmDet3_scaling (a : SqEdges) (s : ℝ) :
    cmDet3 (fun e => s * a e) = s ^ 3 * cmDet3 a := by
  rw [cmDet3_eq_cm3, cm3_scaling, cmDet3_eq_cm3]

end

end CayleyMengerMatrix
end Geometry
end IndisputableMonolith

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import IndisputableMonolith.Geometry.CayleyMengerMatrix
import IndisputableMonolith.Geometry.ReggeRigorousFoundation
import IndisputableMonolith.Geometry.DihedralAngle

/-!
# Dihedral Cosines from Cayley-Menger Cofactors

This module replaces the prose reference in `DihedralAngle.lean` with an
actual Lean definition of the tetrahedral dihedral cosine from
Cayley-Menger cofactors.

For an edge `e = (i,j)`, let `(p,q)` be the two vertices opposite that
edge.  In the Cayley-Menger matrix the vertex rows/columns are shifted by
one, so vertex `v : Fin 4` corresponds to CM index `v.val + 1 : Fin 5`.
The classical cofactor formula is:

```
cos θ_e = C_{p,q} / sqrt (C_{p,p} * C_{q,q})
```

where `C` is the cofactor matrix of the `5 × 5` Cayley-Menger matrix.
This sign convention gives `cos θ = 1/3` for the regular tetrahedron,
matching the standard internal dihedral angle.
-/

namespace IndisputableMonolith
namespace Geometry
namespace DihedralCayleyMenger

open CayleyMengerPolynomial CayleyMengerMatrix ReggeRigorousFoundation
open DihedralAngle

noncomputable section

/-- Convert a tetrahedron vertex index `0..3` to the corresponding
Cayley-Menger matrix index `1..4`. -/
def cmVertexIndex : Fin 4 → Fin 5
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4

/-- For each tetrahedral edge, return the two Cayley-Menger vertex indices
opposite that edge. -/
def oppositeCMVertices : Fin 6 → Fin 5 × Fin 5
  | 0 => (3, 4) -- edge (0,1), opposite vertices 2,3
  | 1 => (2, 4) -- edge (0,2), opposite vertices 1,3
  | 2 => (2, 3) -- edge (0,3), opposite vertices 1,2
  | 3 => (1, 4) -- edge (1,2), opposite vertices 0,3
  | 4 => (1, 3) -- edge (1,3), opposite vertices 0,2
  | 5 => (1, 2) -- edge (2,3), opposite vertices 0,1

/-- The Cayley-Menger cofactor denominator for the dihedral cosine at an
edge. -/
def dihedralDenom3 (a : SqEdges) (e : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  Real.sqrt (cmCofactor3 a p p * cmCofactor3 a q q)

/-- The tetrahedral dihedral cosine from Cayley-Menger cofactors. -/
def dihedralCos3Sq (a : SqEdges) (e : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  cmCofactor3 a p q / dihedralDenom3 a e

/-- The same cosine on a `NonDegenerateTet`. -/
def dihedralCos3 (T : NonDegenerateTet) (e : Fin 6) : ℝ :=
  dihedralCos3Sq T.sqEdge e

/-- The dihedral angle obtained from the cofactor cosine formula. -/
def dihedralAngle3 (T : NonDegenerateTet) (e : Fin 6) : ℝ :=
  Real.arccos (dihedralCos3 T e)

/-- Package the cofactor-defined angle in the existing `DihedralAngleData`
API, assuming the usual range bound for the cofactor cosine. -/
def dihedralAngleData3 (T : NonDegenerateTet) (e : Fin 6)
    (hlo : -1 ≤ dihedralCos3 T e) (hhi : dihedralCos3 T e ≤ 1) :
    DihedralAngleData where
  cosine := dihedralCos3 T e
  cosine_lb := hlo
  cosine_ub := hhi

/-- The regular-tetrahedron cofactor check required to reduce the cofactor
formula to `cos θ = 1 / 3`.  This is isolated so the expensive determinant
minor expansion is not repeated by downstream modules. -/
def RegularUnitCofactorCheck : Prop :=
  ∀ e : Fin 6,
    let p := (oppositeCMVertices e).1
    let q := (oppositeCMVertices e).2
    cmCofactor3 regularUnitSqEdges p q = 1 ∧
      cmCofactor3 regularUnitSqEdges p p = -3 ∧
      cmCofactor3 regularUnitSqEdges q q = -3

/-- The regular-unit cofactor check is now a theorem, not an assumption. -/
theorem regularUnitCofactorCheck : RegularUnitCofactorCheck := by
  intro e
  fin_cases e <;>
    simp [oppositeCMVertices,
      regularUnit_cofactor_34, regularUnit_cofactor_24, regularUnit_cofactor_23,
      regularUnit_cofactor_14, regularUnit_cofactor_13, regularUnit_cofactor_12,
      regularUnit_vertex_diag_cofactor]

/-- If the regular-tetrahedron cofactor check holds, the cofactor formula
gives the standard value `cos θ = 1 / 3`. -/
theorem dihedralCos3_regularUnit_of_cofactorCheck
    (hC : RegularUnitCofactorCheck) (e : Fin 6) :
    dihedralCos3 regularUnitTet e = (1 / 3 : ℝ) := by
  unfold dihedralCos3 dihedralCos3Sq dihedralDenom3
  simp [regularUnitTet]
  rcases hC e with ⟨hnum, hpp, hqq⟩
  rw [hnum, hpp, hqq]
  have hsqrt9 : Real.sqrt 9 = (3 : ℝ) := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)
  norm_num
  rw [hsqrt9]
  norm_num

/-- Hence, under the regular cofactor check, the cofactor angle agrees with
the existing regular-tetrahedron dihedral API. -/
theorem dihedralAngle3_regularUnit_of_cofactorCheck
    (hC : RegularUnitCofactorCheck) (e : Fin 6) :
    dihedralAngle3 regularUnitTet e = regular_tet_dihedral.theta := by
  unfold dihedralAngle3 DihedralAngleData.theta regular_tet_dihedral
  rw [dihedralCos3_regularUnit_of_cofactorCheck hC e]

/-- The cofactor formula gives the standard regular tetrahedron value
`cos θ = 1 / 3` without external assumptions. -/
theorem dihedralCos3_regularUnit (e : Fin 6) :
    dihedralCos3 regularUnitTet e = (1 / 3 : ℝ) :=
  dihedralCos3_regularUnit_of_cofactorCheck regularUnitCofactorCheck e

/-- The cofactor angle agrees with the existing regular-tetrahedron
dihedral API without external assumptions. -/
theorem dihedralAngle3_regularUnit (e : Fin 6) :
    dihedralAngle3 regularUnitTet e = regular_tet_dihedral.theta :=
  dihedralAngle3_regularUnit_of_cofactorCheck regularUnitCofactorCheck e

end

end DihedralCayleyMenger
end Geometry
end IndisputableMonolith

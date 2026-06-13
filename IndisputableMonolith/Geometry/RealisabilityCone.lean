import IndisputableMonolith.Geometry.CayleyMengerMatrix

/-!
# Reallisability Cone for Tetrahedral Squared Edges

This module defines the open domain on which the tetrahedral
Cayley-Menger and dihedral-angle formulas are intended to be used.
-/

namespace IndisputableMonolith
namespace Geometry
namespace RealisabilityCone

open CayleyMengerPolynomial
open CayleyMengerMatrix

noncomputable section

/-- Basic open tetrahedral cone: positive squared edge lengths and positive
Cayley-Menger determinant.  Later phases strengthen this with face-minor
positivity as needed by cofactor denominators. -/
def RealisableTetCone : Set SqEdges :=
  {a | (∀ i : Fin 6, 0 < a i) ∧ 0 < cm3 a}

/-- Membership unpacking: all squared edges are positive. -/
theorem RealisableTetCone.edge_pos {a : SqEdges} (ha : a ∈ RealisableTetCone) :
    ∀ i : Fin 6, 0 < a i :=
  ha.1

/-- Membership unpacking: Cayley-Menger determinant is positive. -/
theorem RealisableTetCone.cm_pos {a : SqEdges} (ha : a ∈ RealisableTetCone) :
    0 < cm3 a :=
  ha.2

/-- The regular unit tetrahedron lies in the basic realisability cone. -/
theorem regularUnit_mem_realisableTetCone :
    regularUnitSqEdges ∈ RealisableTetCone := by
  constructor
  · intro i
    unfold regularUnitSqEdges
    norm_num
  · rw [cm3_regular_unit]
    norm_num

/-- The right-angle unit tetrahedron lies in the basic realisability cone. -/
theorem rightAngleUnit_mem_realisableTetCone :
    rightAngleUnitSqEdges ∈ RealisableTetCone := by
  constructor
  · intro i
    unfold rightAngleUnitSqEdges
    fin_cases i <;> norm_num
  · rw [cm3_rightAngle_unit]
    norm_num

end

end RealisabilityCone
end Geometry
end IndisputableMonolith

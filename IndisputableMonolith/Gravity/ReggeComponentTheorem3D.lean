import Mathlib.Data.Real.Basic
import IndisputableMonolith.Geometry.ReggeHessian3D
import IndisputableMonolith.Gravity.WeakFieldConformalRegge

/-!
# 3D Regge Component Theorem Bridge

This module connects the genuine 3D Regge Hessian package to the existing
weak-field conformal Regge bridge.  The geometric computation supplies a
`GenuineComponentPackage`; this file turns it into the existing
`ReggeComponentComparison` interface and therefore into the Dirichlet-form
reduction already proved in `WeakFieldConformalRegge`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace ReggeComponentTheorem3D

open Geometry.ReggeTriangulation3D
open Geometry.ReggeHessian3D
open WeakFieldConformalRegge
open Foundation.SimplicialLedger.EdgeLengthFromPsi

noncomputable section

/-- The genuine geometric component package produced by the
Cayley-Menger/dihedral/Hessian computation. -/
structure GenuineComponentPackage (K : Triangulation3D) where
  W : WeakFieldReggeData K.nV
  geometricArea : Fin K.nV → Fin K.nV → ℝ
  geometricArea_symm : ∀ i j, geometricArea i j = geometricArea j i
  geometricArea_nonneg : ∀ i j, 0 ≤ geometricArea i j
  offDiag_component_match :
    ∀ i j, i ≠ j → bilinearCoefficient W i j = - geometricArea i j
  schlaefli_row_sum : SchlaefliRowSum W

/-- A genuine component package instantiates the existing comparison
interface. -/
def componentComparison_of_genuine
    {K : Triangulation3D} (G : GenuineComponentPackage K) :
    ReggeComponentComparison G.W where
  geometricArea := G.geometricArea
  geometricArea_symm := G.geometricArea_symm
  geometricArea_nonneg := G.geometricArea_nonneg
  offDiag_component_match := G.offDiag_component_match
  schlaefli_row_sum := G.schlaefli_row_sum

/-- The existing weak-field reduction applies to the genuine component
package. -/
theorem genuine_component_dirichlet_reduction
    {K : Triangulation3D} (G : GenuineComponentPackage K)
    (ε : LogPotential K.nV) :
    secondOrderReggeAction G.W ε =
      (1 / 2) * dirichletForm (edgeArea G.W) ε :=
  weak_field_conformal_reduction G.W G.schlaefli_row_sum ε

end

end ReggeComponentTheorem3D
end Gravity
end IndisputableMonolith

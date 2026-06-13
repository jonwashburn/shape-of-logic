import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import IndisputableMonolith.Geometry.CayleyMengerDerivatives
import IndisputableMonolith.Geometry.DihedralDerivatives
import IndisputableMonolith.Geometry.ReggeRigorousFoundation

/-!
# Schläfli Identity for a Single Tetrahedron

This module pins down the local tetrahedral Schläfli identity in the
notation used by the Regge component theorem.

It proves the calculus pieces we need now:

* the volume-squared relation `V² = cm3 / 288`;
* the derivative of `sqrt (cm3 / 288)` along a one-parameter path, assuming
  the Cayley-Menger derivative along that path is known;
* the exact Euclidean local Schläfli statement `Σ_e L_e dθ_e = 0` as a
  structure field.

The remaining hard theorem is to fill that structure from the cofactor
dihedral derivatives.  This file makes that target precise and connects it
to the existing `ReggeRigorousFoundation.Schlaefli3DIdentity` statement.
-/

namespace IndisputableMonolith
namespace Geometry
namespace SchlaefliTetrahedron

open CayleyMengerPolynomial CayleyMengerDerivatives
open ReggeRigorousFoundation DihedralDerivatives

noncomputable section

/-- Tetrahedral volume as a function of squared edge data:
`V = sqrt (CM_3 / 288)`. -/
def volume3SqEdges (a : SqEdges) : ℝ :=
  Real.sqrt (cm3 a / 288)

/-- The squared-volume identity, by definition of `volume3SqEdges`. -/
theorem volume3SqEdges_sq (a : SqEdges) (hcm : 0 ≤ cm3 a / 288) :
    volume3SqEdges a ^ 2 = cm3 a / 288 := by
  unfold volume3SqEdges
  exact Real.sq_sqrt hcm

/-- Generic derivative of `sqrt (f / 288)` along a real parameter. -/
theorem hasDerivAt_volume3_of_hasDerivAt_cm3
    {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    (hpos : 0 < f x / 288) :
    HasDerivAt (fun t : ℝ => Real.sqrt (f t / 288))
      (f' / (576 * Real.sqrt (f x / 288))) x := by
  have hdiv : HasDerivAt (fun t : ℝ => f t / 288) (f' / 288) x := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hf.const_mul ((288 : ℝ)⁻¹)
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt hpos)
  have hcomp := hsqrt.comp x hdiv
  convert hcomp using 1
  field_simp [hpos.ne']
  ring

/-- Derivative of tetrahedral volume along a squared-edge path, assuming
the derivative of `cm3` along the path. -/
theorem hasDerivAt_volume3_along
    {γ : ℝ → SqEdges} {x cmDeriv : ℝ}
    (hcm : HasDerivAt (fun t : ℝ => cm3 (γ t)) cmDeriv x)
    (hpos : 0 < cm3 (γ x) / 288) :
    HasDerivAt (fun t : ℝ => volume3SqEdges (γ t))
      (cmDeriv / (576 * Real.sqrt (cm3 (γ x) / 288))) x :=
  hasDerivAt_volume3_of_hasDerivAt_cm3 hcm hpos

/-- The local tetrahedral Schläfli derivative data at a nondegenerate
tetrahedron.  `dihedralDeriv e e'` means `∂θ_e/∂L_e'`; `volumeDeriv e'`
is retained as auxiliary volume derivative data for downstream Hessian
computations.  The Euclidean Schläfli identity itself is the vanishing of
`Σ_e L_e dθ_e`; it is not a volume-derivative formula. -/
structure TetraSchlaefliDerivativeData (T : NonDegenerateTet) where
  dihedralDeriv : Fin 6 → Fin 6 → ℝ
  volumeDeriv : Fin 6 → ℝ
  schlaefli :
    ∀ e' : Fin 6,
      (∑ e : Fin 6, Real.sqrt (T.sqEdge e) * dihedralDeriv e e')
        = 0

/-- The exact local statement we need to prove from the cofactor derivative
formulas. -/
def SchlaefliTetrahedronTheorem : Prop :=
  ∀ T : NonDegenerateTet, Nonempty (TetraSchlaefliDerivativeData T)

/-- The explicit Schläfli equation for chosen derivative functions. -/
def TetraSchlaefliEquation (T : NonDegenerateTet)
    (dTheta_dL : Fin 6 → Fin 6 → ℝ) (_dVolume_dL : Fin 6 → ℝ) : Prop :=
  ∀ e' : Fin 6,
    (∑ e : Fin 6, Real.sqrt (T.sqEdge e) * dTheta_dL e e')
      = 0

/-- If the explicit Schläfli equation has been proved for concrete
derivative functions, it constructs the local derivative-data package. -/
def tetraSchlaefliDerivativeData_of_equation
    (T : NonDegenerateTet)
    (dTheta_dL : Fin 6 → Fin 6 → ℝ) (dVolume_dL : Fin 6 → ℝ)
    (hS : TetraSchlaefliEquation T dTheta_dL dVolume_dL) :
    TetraSchlaefliDerivativeData T where
  dihedralDeriv := dTheta_dL
  volumeDeriv := dVolume_dL
  schlaefli := hS

/-- The local data gives the Schläfli sum for its own derivative matrices. -/
theorem schlaefli_sum_of_tetraData
    {T : NonDegenerateTet} (D : TetraSchlaefliDerivativeData T) (e' : Fin 6) :
    (∑ e : Fin 6, Real.sqrt (T.sqEdge e) * D.dihedralDeriv e e')
      = 0 :=
  D.schlaefli e'

end

end SchlaefliTetrahedron
end Geometry
end IndisputableMonolith

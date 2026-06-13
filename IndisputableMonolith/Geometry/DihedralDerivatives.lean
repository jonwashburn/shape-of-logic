import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import IndisputableMonolith.Geometry.CofactorDerivatives
import IndisputableMonolith.Geometry.DihedralCayleyMenger
import IndisputableMonolith.Geometry.DihedralCofactorFormula

/-!
# Dihedral Angle Derivatives

This module isolates the analytic part of the dihedral derivative:
once the Cayley-Menger cofactor cosine has a derivative, the angle
`θ = arccos(cos θ)` has the standard derivative

```
dθ = -(1 / sqrt (1 - cos^2)) · d(cos θ).
```

The remaining hard work is algebraic/geometric: computing the derivative
of `dihedralCos3Sq` from the cofactor minors.  That computation belongs
to the cofactor derivative layer.  This module provides the exact
calculus interface that layer must feed.
-/

namespace IndisputableMonolith
namespace Geometry
namespace DihedralDerivatives

open DihedralCayleyMenger
open CofactorDerivatives
open DihedralCofactorFormula

noncomputable section

/-- Dihedral angle as a function of squared edge data. -/
def dihedralAngle3Sq (a : CayleyMengerPolynomial.SqEdges) (e : Fin 6) : ℝ :=
  Real.arccos (dihedralCos3Sq a e)

/-- Generic derivative of `arccos ∘ f`. -/
theorem hasDerivAt_arccos_comp
    {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x)
    (hm : f x ≠ -1) (hp : f x ≠ 1) :
    HasDerivAt (fun t : ℝ => Real.arccos (f t))
      (-(1 / Real.sqrt (1 - (f x) ^ 2)) * f') x := by
  have hacos := Real.hasDerivAt_arccos hm hp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hacos.comp x hf

/-- Derivative of a dihedral angle along any one-parameter squared-edge path,
assuming the cofactor cosine derivative along that path is known and the
cosine stays away from the arccos endpoints at the base point. -/
theorem hasDerivAt_dihedralAngle3Sq_along
    {γ : ℝ → CayleyMengerPolynomial.SqEdges} {x cosDeriv : ℝ} (e : Fin 6)
    (hcos : HasDerivAt (fun t : ℝ => dihedralCos3Sq (γ t) e) cosDeriv x)
    (hm : dihedralCos3Sq (γ x) e ≠ -1)
    (hp : dihedralCos3Sq (γ x) e ≠ 1) :
    HasDerivAt (fun t : ℝ => dihedralAngle3Sq (γ t) e)
      (-(1 / Real.sqrt (1 - (dihedralCos3Sq (γ x) e) ^ 2)) * cosDeriv) x := by
  exact hasDerivAt_arccos_comp hcos hm hp

/-- The local derivative package needed for a single dihedral angle. -/
structure DihedralAngleDerivativeAlong
    (γ : ℝ → CayleyMengerPolynomial.SqEdges) (e : Fin 6) (x : ℝ) where
  cosDeriv : ℝ
  cos_hasDerivAt :
    HasDerivAt (fun t : ℝ => dihedralCos3Sq (γ t) e) cosDeriv x
  cos_ne_neg_one : dihedralCos3Sq (γ x) e ≠ -1
  cos_ne_one : dihedralCos3Sq (γ x) e ≠ 1

/-- A packaged derivative theorem for downstream Regge modules. -/
theorem DihedralAngleDerivativeAlong.angle_hasDerivAt
    {γ : ℝ → CayleyMengerPolynomial.SqEdges} {e : Fin 6} {x : ℝ}
    (D : DihedralAngleDerivativeAlong γ e x) :
    HasDerivAt (fun t : ℝ => dihedralAngle3Sq (γ t) e)
      (-(1 / Real.sqrt (1 - (dihedralCos3Sq (γ x) e) ^ 2)) * D.cosDeriv) x :=
  hasDerivAt_dihedralAngle3Sq_along e D.cos_hasDerivAt D.cos_ne_neg_one D.cos_ne_one

/-- Interior range is enough to satisfy the endpoint hypotheses for arccos. -/
theorem arccos_endpoint_hypotheses_of_interior {c : ℝ}
    (hlo : -1 < c) (hhi : c < 1) : c ≠ -1 ∧ c ≠ 1 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Endpoint hypotheses for a cofactor cosine coming from a realized
tetrahedron, provided the endpoint cases are excluded. -/
theorem arccos_endpoint_hypotheses_of_realized_ne_endpoints
    (T : TetrahedronRealization.RealizedTet) (e : Fin 6)
    (hneg : dihedralCos3Sq (TetrahedronRealization.sqEdgeOfPoints T) e ≠ -1)
    (hpos : dihedralCos3Sq (TetrahedronRealization.sqEdgeOfPoints T) e ≠ 1) :
    dihedralCos3Sq (TetrahedronRealization.sqEdgeOfPoints T) e ≠ -1 ∧
      dihedralCos3Sq (TetrahedronRealization.sqEdgeOfPoints T) e ≠ 1 :=
  ⟨hneg, hpos⟩

/-- Dihedral angle derivative generated directly from Cayley-Menger cofactor
derivatives for the numerator and the two diagonal denominator cofactors. -/
theorem hasDerivAt_dihedralAngle3Sq_from_cofactors
    {γ : ℝ → CayleyMengerPolynomial.SqEdges} {x num' pp' qq' : ℝ} (e : Fin 6)
    (hnum : HasDerivAt
      (fun t : ℝ =>
        let p := (oppositeCMVertices e).1
        let q := (oppositeCMVertices e).2
        CayleyMengerMatrix.cmCofactor3 (γ t) p q) num' x)
    (hpp : HasDerivAt
      (fun t : ℝ =>
        let p := (oppositeCMVertices e).1
        CayleyMengerMatrix.cmCofactor3 (γ t) p p) pp' x)
    (hqq : HasDerivAt
      (fun t : ℝ =>
        let q := (oppositeCMVertices e).2
        CayleyMengerMatrix.cmCofactor3 (γ t) q q) qq' x)
    (hprod_ne :
      (let p := (oppositeCMVertices e).1
       let q := (oppositeCMVertices e).2
       CayleyMengerMatrix.cmCofactor3 (γ x) p p *
         CayleyMengerMatrix.cmCofactor3 (γ x) q q) ≠ 0)
    (hden_ne : dihedralDenom3 (γ x) e ≠ 0)
    (hm : dihedralCos3Sq (γ x) e ≠ -1)
    (hp : dihedralCos3Sq (γ x) e ≠ 1) :
    HasDerivAt (fun t : ℝ => dihedralAngle3Sq (γ t) e)
      (-(1 / Real.sqrt (1 - (dihedralCos3Sq (γ x) e) ^ 2)) *
        dihedralCos3SqDerivValue γ x num'
          (dihedralDenom3DerivValue γ x pp' qq' e) e) x := by
  exact hasDerivAt_dihedralAngle3Sq_along e
    (hasDerivAt_dihedralCos3Sq_from_cofactors e hnum hpp hqq hprod_ne hden_ne)
    hm hp

/-! ## Closed-form derivative values

The next definition is the concrete arccos-chain-rule value obtained after
substituting the cofactor partial polynomials exposed in
`CofactorDerivatives`.  The actual `HasDerivAt` theorem reduces to proving
the cofactor-polynomial coordinate derivative for the needed minors.
-/

/-- Closed-form coordinate derivative value for the tetrahedral dihedral
angle, as a function of squared edge coordinates. -/
def dihedralAngle3SqClosedFormDeriv
    (a : CayleyMengerPolynomial.SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  -(1 / Real.sqrt (1 - (dihedralCos3Sq a e) ^ 2)) *
    dihedralCos3SqClosedFormDeriv a e k

/-- The closed-form angle derivative is the arccos chain-rule multiplier
applied to the closed-form cofactor-ratio derivative. -/
theorem dihedralAngle3SqClosedFormDeriv_def
    (a : CayleyMengerPolynomial.SqEdges) (e : Fin 6) (k : Fin 6) :
    dihedralAngle3SqClosedFormDeriv a e k =
      -(1 / Real.sqrt (1 - (dihedralCos3Sq a e) ^ 2)) *
        dihedralCos3SqClosedFormDeriv a e k := rfl

/-- Explicit coordinate derivative of the cofactor-defined tetrahedral
dihedral angle. -/
theorem hasDerivAt_dihedralAngle3Sq_explicit
    (a : CayleyMengerPolynomial.SqEdges) (e k : Fin 6)
    (hprod_ne :
      (let p := (oppositeCMVertices e).1
       let q := (oppositeCMVertices e).2
       CayleyMengerMatrix.cmCofactor3 a p p *
         CayleyMengerMatrix.cmCofactor3 a q q) ≠ 0)
    (hden_ne : dihedralDenom3 a e ≠ 0)
    (hm : dihedralCos3Sq a e ≠ -1)
    (hp : dihedralCos3Sq a e ≠ 1) :
    HasDerivAt (fun t : ℝ => dihedralAngle3Sq (Function.update a k t) e)
      (dihedralAngle3SqClosedFormDeriv a e k) (a k) := by
  have hbase :
      Function.update a k (a k) = a := by
    funext i
    by_cases hi : i = k <;> simp [Function.update, hi]
  have hm' : dihedralCos3Sq (Function.update a k (a k)) e ≠ -1 := by
    simpa [hbase] using hm
  have hp' : dihedralCos3Sq (Function.update a k (a k)) e ≠ 1 := by
    simpa [hbase] using hp
  simpa [dihedralAngle3SqClosedFormDeriv] using
    hasDerivAt_dihedralAngle3Sq_along e
      (hasDerivAt_dihedralCos3Sq_explicit a e k hprod_ne hden_ne)
      hm' hp'

end

end DihedralDerivatives
end Geometry
end IndisputableMonolith

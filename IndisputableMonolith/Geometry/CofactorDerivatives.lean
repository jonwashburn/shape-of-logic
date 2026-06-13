import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import IndisputableMonolith.Geometry.DihedralCayleyMenger
import IndisputableMonolith.Geometry.RealisabilityCone
import IndisputableMonolith.Geometry.CofactorPolynomial

/-!
# Cayley-Menger Cofactor Derivative Interfaces

This module exposes derivative hooks for Cayley-Menger cofactors and the
dihedral cofactor ratio.  The hard symbolic derivative simplifications
are still downstream, but the calculus layer is no longer implicit.
-/

namespace IndisputableMonolith
namespace Geometry
namespace CofactorDerivatives

open CayleyMengerPolynomial
open CayleyMengerMatrix
open DihedralCayleyMenger
open CofactorPolynomial

noncomputable section

/-- Canonical Fréchet derivative of a Cayley-Menger cofactor. -/
def cmCofactor3FDeriv (r c : Fin 5) (a : SqEdges) : SqEdges →L[ℝ] ℝ :=
  fderiv ℝ (fun x : SqEdges => cmCofactor3 x r c) a

/-- Cofactors are differentiable everywhere because they are smooth
polynomial functions of the squared-edge coordinates. -/
theorem hasFDerivAt_cmCofactor3 (r c : Fin 5) (a : SqEdges) :
    HasFDerivAt (fun x : SqEdges => cmCofactor3 x r c)
      (cmCofactor3FDeriv r c a) a := by
  unfold cmCofactor3FDeriv
  exact ((cmCofactor3_contDiff 1 r c).differentiable_one a).hasFDerivAt

/-- Generic derivative of a quotient `num / den` along a real parameter. -/
theorem hasDerivAt_div
    {num den : ℝ → ℝ} {num' den' x : ℝ}
    (hnum : HasDerivAt num num' x)
    (hden : HasDerivAt den den' x)
    (hden_ne : den x ≠ 0) :
    HasDerivAt (fun t : ℝ => num t / den t)
      ((num' * den x - num x * den') / (den x) ^ 2) x := by
  have h := hnum.div hden hden_ne
  convert h using 1

/-- Derivative of `dihedralCos3Sq` along a squared-edge path, provided the
numerator and denominator derivatives along that path. -/
theorem hasDerivAt_dihedralCos3Sq_along
    {γ : ℝ → SqEdges} {x num' den' : ℝ} (e : Fin 6)
    (hnum : HasDerivAt
      (fun t : ℝ =>
        let p := (oppositeCMVertices e).1
        let q := (oppositeCMVertices e).2
        cmCofactor3 (γ t) p q) num' x)
    (hden : HasDerivAt (fun t : ℝ => dihedralDenom3 (γ t) e) den' x)
    (hden_ne : dihedralDenom3 (γ x) e ≠ 0) :
    HasDerivAt (fun t : ℝ => dihedralCos3Sq (γ t) e)
      ((num' * dihedralDenom3 (γ x) e -
          (let p := (oppositeCMVertices e).1
           let q := (oppositeCMVertices e).2
           cmCofactor3 (γ x) p q) * den') /
        (dihedralDenom3 (γ x) e) ^ 2) x := by
  unfold dihedralCos3Sq
  exact hasDerivAt_div hnum hden hden_ne

/-- Derivative of the square-root denominator
`sqrt(C_pp * C_qq)` along a squared-edge path. -/
theorem hasDerivAt_dihedralDenom3_along
    {γ : ℝ → SqEdges} {x pp' qq' : ℝ} (e : Fin 6)
    (hpp : HasDerivAt
      (fun t : ℝ =>
        let p := (oppositeCMVertices e).1
        cmCofactor3 (γ t) p p) pp' x)
    (hqq : HasDerivAt
      (fun t : ℝ =>
        let q := (oppositeCMVertices e).2
        cmCofactor3 (γ t) q q) qq' x)
    (hprod_ne :
      (let p := (oppositeCMVertices e).1
       let q := (oppositeCMVertices e).2
       cmCofactor3 (γ x) p p * cmCofactor3 (γ x) q q) ≠ 0) :
    HasDerivAt (fun t : ℝ => dihedralDenom3 (γ t) e)
      (((let p := (oppositeCMVertices e).1
         let q := (oppositeCMVertices e).2
         pp' * cmCofactor3 (γ x) q q +
           cmCofactor3 (γ x) p p * qq') /
        (2 * dihedralDenom3 (γ x) e))) x := by
  unfold dihedralDenom3
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  have hprod : HasDerivAt
      (fun t : ℝ => cmCofactor3 (γ t) p p * cmCofactor3 (γ t) q q)
      (pp' * cmCofactor3 (γ x) q q + cmCofactor3 (γ x) p p * qq') x := by
    exact hpp.mul hqq
  have hsqrt := Real.hasDerivAt_sqrt hprod_ne
  have hcomp := hsqrt.comp x hprod
  simpa [p, q, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcomp

/-- Value of the derivative of the cofactor denominator along a path, given
the derivatives of the two diagonal cofactors. -/
def dihedralDenom3DerivValue
    (γ : ℝ → SqEdges) (x pp' qq' : ℝ) (e : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  (pp' * cmCofactor3 (γ x) q q + cmCofactor3 (γ x) p p * qq') /
    (2 * dihedralDenom3 (γ x) e)

/-- Value of the derivative of the cofactor-ratio cosine along a path. -/
def dihedralCos3SqDerivValue
    (γ : ℝ → SqEdges) (x num' den' : ℝ) (e : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  (num' * dihedralDenom3 (γ x) e - cmCofactor3 (γ x) p q * den') /
    (dihedralDenom3 (γ x) e) ^ 2

/-! ## Closed-form coordinate derivative values

The next definitions specialize the abstract numerator/denominator derivative
values above to the explicit cofactor partial polynomials from
`CofactorPolynomial`.  They are the concrete expressions used by the
Schläfli and Hessian closure targets.
-/

/-- Closed-form derivative of the numerator cofactor for edge `e` with
respect to squared-edge coordinate `k`. -/
def dihedralNumeratorClosedDeriv (a : SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  cmCofactorPartial p q k a

/-- Closed-form derivative of the left diagonal denominator cofactor. -/
def dihedralLeftDiagClosedDeriv (a : SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  cmCofactorPartial p p k a

/-- Closed-form derivative of the right diagonal denominator cofactor. -/
def dihedralRightDiagClosedDeriv (a : SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  let q := (oppositeCMVertices e).2
  cmCofactorPartial q q k a

/-- Closed-form derivative of the square-root cofactor denominator. -/
def dihedralDenom3ClosedDerivValue (a : SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  (dihedralLeftDiagClosedDeriv a e k * cmCofactor3 a q q +
      cmCofactor3 a p p * dihedralRightDiagClosedDeriv a e k) /
    (2 * dihedralDenom3 a e)

/-- Closed-form coordinate derivative value for the cofactor-ratio cosine. -/
def dihedralCos3SqClosedFormDeriv (a : SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  (dihedralNumeratorClosedDeriv a e k * dihedralDenom3 a e -
      cmCofactor3 a p q * dihedralDenom3ClosedDerivValue a e k) /
    (dihedralDenom3 a e) ^ 2

/-- Polynomial-cofactor denominator for the same cofactor cosine.  This is
definitionally lighter than `dihedralDenom3` because it avoids determinant
normalization. -/
def dihedralDenom3Poly (a : SqEdges) (e : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  Real.sqrt (cmCofactor3Poly p p a * cmCofactor3Poly q q a)

/-- Product of the two diagonal polynomial cofactors used in a dihedral
cosine denominator. -/
def dihedralCofactorProductPoly (a : SqEdges) (e : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  cmCofactor3Poly p p a * cmCofactor3Poly q q a

/-- Numerator polynomial cofactor used in a dihedral cosine. -/
def dihedralCofactorNumeratorPoly (a : SqEdges) (e : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  cmCofactor3Poly p q a

/-- Polynomial-cofactor cosine, avoiding determinant normalization. -/
def dihedralCos3SqPoly (a : SqEdges) (e : Fin 6) : ℝ :=
  dihedralCofactorNumeratorPoly a e / dihedralDenom3Poly a e

/-- Polynomial-cofactor derivative of the square-root denominator. -/
def dihedralDenom3PolyClosedDerivValue (a : SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  (cmCofactorPartial p p k a * cmCofactor3Poly q q a +
      cmCofactor3Poly p p a * cmCofactorPartial q q k a) /
    (2 * dihedralDenom3Poly a e)

/-- Polynomial-cofactor closed-form derivative of the cofactor-ratio cosine. -/
def dihedralCos3SqPolyClosedFormDeriv (a : SqEdges) (e : Fin 6) (k : Fin 6) : ℝ :=
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  (cmCofactorPartial p q k a * dihedralDenom3Poly a e -
      cmCofactor3Poly p q a * dihedralDenom3PolyClosedDerivValue a e k) /
    (dihedralDenom3Poly a e) ^ 2

theorem dihedralDenom3_eq_poly (a : SqEdges) (e : Fin 6) :
    dihedralDenom3 a e = dihedralDenom3Poly a e := by
  unfold dihedralDenom3 dihedralDenom3Poly
  simp_rw [cmCofactor3_eq_poly]

theorem dihedralCos3Sq_eq_poly (a : SqEdges) (e : Fin 6) :
    dihedralCos3Sq a e = dihedralCos3SqPoly a e := by
  unfold dihedralCos3Sq dihedralCos3SqPoly dihedralCofactorNumeratorPoly
  rw [dihedralDenom3_eq_poly]
  simp_rw [cmCofactor3_eq_poly]

theorem dihedralDenom3ClosedDerivValue_eq_poly (a : SqEdges) (e : Fin 6) (k : Fin 6) :
    dihedralDenom3ClosedDerivValue a e k =
      dihedralDenom3PolyClosedDerivValue a e k := by
  unfold dihedralDenom3ClosedDerivValue dihedralDenom3PolyClosedDerivValue
    dihedralLeftDiagClosedDeriv dihedralRightDiagClosedDeriv
  rw [dihedralDenom3_eq_poly]
  simp_rw [cmCofactor3_eq_poly]

theorem dihedralCos3SqClosedFormDeriv_eq_poly (a : SqEdges) (e : Fin 6) (k : Fin 6) :
    dihedralCos3SqClosedFormDeriv a e k =
      dihedralCos3SqPolyClosedFormDeriv a e k := by
  unfold dihedralCos3SqClosedFormDeriv dihedralCos3SqPolyClosedFormDeriv
    dihedralNumeratorClosedDeriv
  rw [dihedralDenom3_eq_poly, dihedralDenom3ClosedDerivValue_eq_poly]
  simp_rw [cmCofactor3_eq_poly]

/-- Polynomial cofactor discriminant written in the notation of an edge's
cofactor cosine denominator. -/
theorem dihedralCofactorPoly_discriminant_eq (a : SqEdges) (e : Fin 6) :
    let p := (oppositeCMVertices e).1
    let q := (oppositeCMVertices e).2
    cmCofactor3Poly p p a * cmCofactor3Poly q q a -
        cmCofactor3Poly p q a ^ 2 =
      2 * cm3 a * a e :=
  cmCofactor_discriminant_eq a e

theorem dihedralDenom3Poly_sq
    (a : SqEdges) (e : Fin 6)
    (hprod_nonneg : 0 ≤ dihedralCofactorProductPoly a e) :
    dihedralDenom3Poly a e ^ 2 = dihedralCofactorProductPoly a e := by
  unfold dihedralDenom3Poly dihedralCofactorProductPoly
  exact Real.sq_sqrt hprod_nonneg

/-- Radical-free expression for `1 - cos^2` using the Cayley cofactor
discriminant identity. -/
theorem one_sub_dihedralCos3SqPoly_sq_eq
    (a : SqEdges) (e : Fin 6)
    (hprod_nonneg : 0 ≤ dihedralCofactorProductPoly a e)
    (hprod_ne : dihedralCofactorProductPoly a e ≠ 0)
    (hden_ne : dihedralDenom3Poly a e ≠ 0) :
    1 - (dihedralCos3SqPoly a e) ^ 2 =
      (2 * cm3 a * a e) / dihedralCofactorProductPoly a e := by
  have hden_sq := dihedralDenom3Poly_sq a e hprod_nonneg
  unfold dihedralCos3SqPoly dihedralCofactorNumeratorPoly
  calc
    1 - (dihedralCofactorNumeratorPoly a e / dihedralDenom3Poly a e) ^ 2
        = (dihedralCofactorProductPoly a e - dihedralCofactorNumeratorPoly a e ^ 2) /
            dihedralCofactorProductPoly a e := by
          field_simp [hden_ne, hprod_ne]
          rw [← hden_sq]
          ring
    _ = (2 * cm3 a * a e) / dihedralCofactorProductPoly a e := by
          unfold dihedralCofactorProductPoly dihedralCofactorNumeratorPoly
          rw [dihedralCofactorPoly_discriminant_eq]

/-- Square-root normalization of the arccos denominator after applying the
Cayley cofactor discriminant identity. -/
theorem sqrt_one_sub_dihedralCos3SqPoly_sq_eq
    (a : SqEdges) (e : Fin 6)
    (hprod_nonneg : 0 ≤ dihedralCofactorProductPoly a e)
    (hprod_ne : dihedralCofactorProductPoly a e ≠ 0)
    (hden_ne : dihedralDenom3Poly a e ≠ 0)
    (hnum_nonneg : 0 ≤ 2 * cm3 a * a e) :
    Real.sqrt (1 - (dihedralCos3SqPoly a e) ^ 2) =
      Real.sqrt (2 * cm3 a * a e) / dihedralDenom3Poly a e := by
  rw [one_sub_dihedralCos3SqPoly_sq_eq a e hprod_nonneg hprod_ne hden_ne]
  rw [Real.sqrt_div hnum_nonneg]
  simp [dihedralDenom3Poly, dihedralCofactorProductPoly]

/-- Nondegenerate tetrahedra have positive polynomial cofactor denominator
products for every dihedral edge. -/
theorem dihedralCofactorProductPoly_pos_of_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (e : Fin 6) :
    0 < dihedralCofactorProductPoly T.sqEdge e := by
  have hdisc := dihedralCofactorPoly_discriminant_eq T.sqEdge e
  have hdisc' :
      dihedralCofactorProductPoly T.sqEdge e -
          dihedralCofactorNumeratorPoly T.sqEdge e ^ 2 =
        2 * cm3 T.sqEdge * T.sqEdge e := by
    simpa [dihedralCofactorProductPoly, dihedralCofactorNumeratorPoly] using hdisc
  have hpos : 0 < 2 * cm3 T.sqEdge * T.sqEdge e := by
    nlinarith [T.cm_pos, T.sqEdge_pos e]
  have hsq : 0 ≤ dihedralCofactorNumeratorPoly T.sqEdge e ^ 2 := sq_nonneg _
  nlinarith

theorem dihedralCofactorProductPoly_nonneg_of_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (e : Fin 6) :
    0 ≤ dihedralCofactorProductPoly T.sqEdge e :=
  le_of_lt (dihedralCofactorProductPoly_pos_of_nonDegenerate T e)

theorem dihedralCofactorProductPoly_ne_zero_of_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (e : Fin 6) :
    dihedralCofactorProductPoly T.sqEdge e ≠ 0 :=
  ne_of_gt (dihedralCofactorProductPoly_pos_of_nonDegenerate T e)

theorem dihedralDenom3Poly_pos_of_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (e : Fin 6) :
    0 < dihedralDenom3Poly T.sqEdge e := by
  unfold dihedralDenom3Poly
  rw [Real.sqrt_pos]
  simpa [dihedralCofactorProductPoly] using
    dihedralCofactorProductPoly_pos_of_nonDegenerate T e

theorem dihedralDenom3Poly_ne_zero_of_nonDegenerate
    (T : ReggeRigorousFoundation.NonDegenerateTet) (e : Fin 6) :
    dihedralDenom3Poly T.sqEdge e ≠ 0 :=
  ne_of_gt (dihedralDenom3Poly_pos_of_nonDegenerate T e)

/-- The closed-form cosine derivative is exactly the generic quotient
derivative value after substituting the explicit cofactor partials. -/
theorem dihedralCos3SqClosedFormDeriv_eq_generic
    (a : SqEdges) (e : Fin 6) (k : Fin 6) :
    dihedralCos3SqClosedFormDeriv a e k =
      dihedralCos3SqDerivValue (fun _ : ℝ => a) 0
        (dihedralNumeratorClosedDeriv a e k)
        (dihedralDenom3ClosedDerivValue a e k) e := by
  unfold dihedralCos3SqClosedFormDeriv dihedralCos3SqDerivValue
  simp

/-- Dihedral cosine derivative from the numerator and diagonal cofactor
derivatives. -/
theorem hasDerivAt_dihedralCos3Sq_from_cofactors
    {γ : ℝ → SqEdges} {x num' pp' qq' : ℝ} (e : Fin 6)
    (hnum : HasDerivAt
      (fun t : ℝ =>
        let p := (oppositeCMVertices e).1
        let q := (oppositeCMVertices e).2
        cmCofactor3 (γ t) p q) num' x)
    (hpp : HasDerivAt
      (fun t : ℝ =>
        let p := (oppositeCMVertices e).1
        cmCofactor3 (γ t) p p) pp' x)
    (hqq : HasDerivAt
      (fun t : ℝ =>
        let q := (oppositeCMVertices e).2
        cmCofactor3 (γ t) q q) qq' x)
    (hprod_ne :
      (let p := (oppositeCMVertices e).1
       let q := (oppositeCMVertices e).2
       cmCofactor3 (γ x) p p * cmCofactor3 (γ x) q q) ≠ 0)
    (hden_ne : dihedralDenom3 (γ x) e ≠ 0) :
    HasDerivAt (fun t : ℝ => dihedralCos3Sq (γ t) e)
      (dihedralCos3SqDerivValue γ x num'
        (dihedralDenom3DerivValue γ x pp' qq' e) e) x := by
  refine hasDerivAt_dihedralCos3Sq_along e hnum ?_ hden_ne
  simpa [dihedralDenom3DerivValue] using
    hasDerivAt_dihedralDenom3_along e hpp hqq hprod_ne

/-- Explicit coordinate derivative of the Cayley-Menger cofactor cosine. -/
theorem hasDerivAt_dihedralCos3Sq_explicit
    (a : SqEdges) (e k : Fin 6)
    (hprod_ne :
      (let p := (oppositeCMVertices e).1
       let q := (oppositeCMVertices e).2
       cmCofactor3 a p p * cmCofactor3 a q q) ≠ 0)
    (hden_ne : dihedralDenom3 a e ≠ 0) :
    HasDerivAt (fun t : ℝ => dihedralCos3Sq (Function.update a k t) e)
      (dihedralCos3SqClosedFormDeriv a e k) (a k) := by
  let p := (oppositeCMVertices e).1
  let q := (oppositeCMVertices e).2
  have hnum :
      HasDerivAt
        (fun t : ℝ =>
          let p := (oppositeCMVertices e).1
          let q := (oppositeCMVertices e).2
          cmCofactor3 (Function.update a k t) p q)
        (dihedralNumeratorClosedDeriv a e k) (a k) := by
    simpa [dihedralNumeratorClosedDeriv, p, q] using
      hasDerivAt_cmCofactor3_along_coord p q k a
  have hpp :
      HasDerivAt
        (fun t : ℝ =>
          let p := (oppositeCMVertices e).1
          cmCofactor3 (Function.update a k t) p p)
        (dihedralLeftDiagClosedDeriv a e k) (a k) := by
    simpa [dihedralLeftDiagClosedDeriv, p] using
      hasDerivAt_cmCofactor3_along_coord p p k a
  have hqq :
      HasDerivAt
        (fun t : ℝ =>
          let q := (oppositeCMVertices e).2
          cmCofactor3 (Function.update a k t) q q)
        (dihedralRightDiagClosedDeriv a e k) (a k) := by
    simpa [dihedralRightDiagClosedDeriv, q] using
      hasDerivAt_cmCofactor3_along_coord q q k a
  have hbase :
      Function.update a k (a k) = a := by
    funext i
    by_cases hi : i = k <;> simp [Function.update, hi]
  have h :=
    hasDerivAt_dihedralCos3Sq_from_cofactors
      (γ := fun t : ℝ => Function.update a k t) (x := a k)
      (num' := dihedralNumeratorClosedDeriv a e k)
      (pp' := dihedralLeftDiagClosedDeriv a e k)
      (qq' := dihedralRightDiagClosedDeriv a e k)
      e hnum hpp hqq ?_ ?_
  · simpa [dihedralCos3SqClosedFormDeriv, dihedralCos3SqDerivValue,
      dihedralDenom3ClosedDerivValue, dihedralDenom3DerivValue,
      dihedralNumeratorClosedDeriv, dihedralLeftDiagClosedDeriv,
      dihedralRightDiagClosedDeriv, hbase, p, q] using h
  · simpa [hbase, p, q] using hprod_ne
  · simpa [hbase] using hden_ne

end

end CofactorDerivatives
end Geometry
end IndisputableMonolith

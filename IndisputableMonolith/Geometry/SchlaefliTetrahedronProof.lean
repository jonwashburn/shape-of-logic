import IndisputableMonolith.Geometry.SchlaefliTetrahedron
import IndisputableMonolith.Geometry.DihedralDerivatives
import IndisputableMonolith.Geometry.AffineIndepInterior

/-!
# Closed-Form Tetrahedral Schläfli Target

This module connects the explicit Cayley-Menger and dihedral derivative
values to the local tetrahedral Schläfli package.  The hard remaining
content is now a single closed-form identity, not an implicit external
field.
-/

namespace IndisputableMonolith
namespace Geometry
namespace SchlaefliTetrahedronProof

open CayleyMengerPolynomial
open CayleyMengerDerivatives
open DihedralDerivatives
open SchlaefliTetrahedron
open ReggeRigorousFoundation
open AffineIndepInterior

noncomputable section

/-- Closed-form derivative value for `V = sqrt (cm3 / 288)` with respect
to a squared-edge coordinate. -/
def volume3ClosedDerivSq (a : SqEdges) (k : Fin 6) : ℝ :=
  cm3_grad a k / (576 * Real.sqrt (cm3 a / 288))

/-- The closed-form squared-edge derivative of tetrahedral volume is the
actual derivative of `volume3SqEdges`. -/
theorem hasDerivAt_volume3ClosedDerivSq
    (T : NonDegenerateTet) (k : Fin 6) :
    HasDerivAt
      (fun t : ℝ => volume3SqEdges (Function.update T.sqEdge k t))
      (volume3ClosedDerivSq T.sqEdge k) (T.sqEdge k) := by
  unfold volume3ClosedDerivSq
  have hbase : Function.update T.sqEdge k (T.sqEdge k) = T.sqEdge := by
    funext i
    by_cases hi : i = k <;> simp [Function.update, hi]
  have h := hasDerivAt_volume3_along
    (γ := fun t : ℝ => Function.update T.sqEdge k t)
    (x := T.sqEdge k)
    (cmDeriv := cm3_grad T.sqEdge k)
    (hasDerivAt_cm3_grad T.sqEdge k)
    (by
      have h288 : (0 : ℝ) < 288 := by norm_num
      simpa [hbase] using div_pos T.cm_pos h288)
  simpa [hbase] using h

/-- Closed-form derivative value for the dihedral angle at edge `e` with
respect to squared-edge coordinate `k`. -/
def dihedralClosedDerivSq (T : NonDegenerateTet) (e k : Fin 6) : ℝ :=
  dihedralAngle3SqClosedFormDeriv T.sqEdge e k

/-- Polynomial-cofactor version of the squared-edge dihedral derivative
value.  This is definitionally lighter than `dihedralClosedDerivSq` and is
the preferred target for the six algebraic Schläfli identities. -/
def dihedralClosedDerivSqPoly (T : NonDegenerateTet) (e k : Fin 6) : ℝ :=
  -(1 / Real.sqrt (1 - (CofactorDerivatives.dihedralCos3SqPoly T.sqEdge e) ^ 2)) *
    CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv T.sqEdge e k

theorem dihedralClosedDerivSq_eq_poly
    (T : NonDegenerateTet) (e k : Fin 6) :
    dihedralClosedDerivSq T e k = dihedralClosedDerivSqPoly T e k := by
  unfold dihedralClosedDerivSq dihedralClosedDerivSqPoly
  unfold DihedralDerivatives.dihedralAngle3SqClosedFormDeriv
  rw [CofactorDerivatives.dihedralCos3Sq_eq_poly]
  rw [CofactorDerivatives.dihedralCos3SqClosedFormDeriv_eq_poly]

/-- The square map derivative at the positive edge length `sqrt (a k)`.
This is the scalar chain-rule factor behind `d/dL = 2L d/da`. -/
theorem hasDerivAt_sqEdgeCoordinate_from_edgeLength
    (T : NonDegenerateTet) (k : Fin 6) :
    HasDerivAt (fun L : ℝ => L ^ 2)
      (2 * Real.sqrt (T.sqEdge k)) (Real.sqrt (T.sqEdge k)) := by
  have h := (hasDerivAt_id (Real.sqrt (T.sqEdge k))).pow 2
  simpa [pow_succ, two_mul, mul_comm, mul_left_comm, mul_assoc] using h

/-- Convert a squared-edge derivative of volume to an edge-length derivative. -/
def volume3ClosedDerivLength (T : NonDegenerateTet) (k : Fin 6) : ℝ :=
  2 * Real.sqrt (T.sqEdge k) * volume3ClosedDerivSq T.sqEdge k

/-- The closed-form edge-length derivative of volume is obtained from the
squared-edge derivative by `d(a_k)/dL_k = 2 L_k`. -/
theorem hasDerivAt_volume3ClosedDerivLength
    (T : NonDegenerateTet) (k : Fin 6) :
    HasDerivAt
      (fun L : ℝ => volume3SqEdges (Function.update T.sqEdge k (L ^ 2)))
      (volume3ClosedDerivLength T k) (Real.sqrt (T.sqEdge k)) := by
  unfold volume3ClosedDerivLength
  have hsq := hasDerivAt_sqEdgeCoordinate_from_edgeLength T k
  have hsqsqrt : Real.sqrt (T.sqEdge k) ^ 2 = T.sqEdge k :=
    Real.sq_sqrt (le_of_lt (T.sqEdge_pos k))
  have hvol : HasDerivAt
      (fun t : ℝ => volume3SqEdges (Function.update T.sqEdge k t))
      (volume3ClosedDerivSq T.sqEdge k)
      (Real.sqrt (T.sqEdge k) ^ 2) := by
    simpa [hsqsqrt] using hasDerivAt_volume3ClosedDerivSq T k
  have hcomp := HasDerivAt.comp_of_eq
    (x := Real.sqrt (T.sqEdge k)) hvol hsq rfl
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcomp

/-- Convert a squared-edge derivative of a dihedral angle to an edge-length
derivative. -/
def dihedralClosedDerivLength (T : NonDegenerateTet) (e k : Fin 6) : ℝ :=
  2 * Real.sqrt (T.sqEdge k) * dihedralClosedDerivSq T e k

/-- The closed-form edge-length derivative of a dihedral angle is obtained
from the squared-edge derivative by `d(a_k)/dL_k = 2 L_k`, under the local
smoothness hypotheses for the cofactor angle. -/
theorem hasDerivAt_dihedralClosedDerivLength
    (T : NonDegenerateTet) (e k : Fin 6)
    (hprod_ne :
      (let p := DihedralCayleyMenger.oppositeCMVertices e |>.1
       let q := DihedralCayleyMenger.oppositeCMVertices e |>.2
       CayleyMengerMatrix.cmCofactor3 T.sqEdge p p *
         CayleyMengerMatrix.cmCofactor3 T.sqEdge q q) ≠ 0)
    (hden_ne : DihedralCayleyMenger.dihedralDenom3 T.sqEdge e ≠ 0)
    (hm : DihedralCayleyMenger.dihedralCos3Sq T.sqEdge e ≠ -1)
    (hp : DihedralCayleyMenger.dihedralCos3Sq T.sqEdge e ≠ 1) :
    HasDerivAt
      (fun L : ℝ =>
        dihedralAngle3Sq (Function.update T.sqEdge k (L ^ 2)) e)
      (dihedralClosedDerivLength T e k) (Real.sqrt (T.sqEdge k)) := by
  unfold dihedralClosedDerivLength dihedralClosedDerivSq
  have hsq := hasDerivAt_sqEdgeCoordinate_from_edgeLength T k
  have hsqsqrt : Real.sqrt (T.sqEdge k) ^ 2 = T.sqEdge k :=
    Real.sq_sqrt (le_of_lt (T.sqEdge_pos k))
  have hangle : HasDerivAt
      (fun t : ℝ => dihedralAngle3Sq (Function.update T.sqEdge k t) e)
      (dihedralAngle3SqClosedFormDeriv T.sqEdge e k)
      (Real.sqrt (T.sqEdge k) ^ 2) := by
    simpa [hsqsqrt] using
      hasDerivAt_dihedralAngle3Sq_explicit T.sqEdge e k hprod_ne hden_ne hm hp
  have hcomp := HasDerivAt.comp_of_eq
    (x := Real.sqrt (T.sqEdge k)) hangle hsq rfl
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcomp

/-- The local Schläfli equation with the old squared-edge derivative
coordinates.  This is kept only as an internal algebraic target; the actual
Schläfli package below uses edge-length derivatives. -/
def TetraSchlaefliClosedEquationSq (T : NonDegenerateTet) : Prop :=
  TetraSchlaefliEquation T
    (fun e k => dihedralClosedDerivSq T e k)
    (fun k => volume3ClosedDerivSq T.sqEdge k)

/-- The local Schläfli equation after converting closed-form squared-edge
derivatives to edge-length derivatives. -/
def TetraSchlaefliClosedEquation (T : NonDegenerateTet) : Prop :=
  TetraSchlaefliEquation T
    (fun e k => dihedralClosedDerivLength T e k)
    (fun k => volume3ClosedDerivLength T k)

/-- The corrected edge-length Schläfli equation follows from the squared-edge
closed-form equation by multiplying the fixed-coordinate equation by
`2 * sqrt (a_k)`. -/
theorem TetraSchlaefliClosedEquation_of_sq
    (T : NonDegenerateTet)
    (hSq : TetraSchlaefliClosedEquationSq T) :
    TetraSchlaefliClosedEquation T := by
  intro k
  unfold dihedralClosedDerivLength
  unfold TetraSchlaefliClosedEquationSq TetraSchlaefliEquation at hSq
  have h := hSq k
  calc
    (∑ e : Fin 6,
        Real.sqrt (T.sqEdge e) *
          (2 * Real.sqrt (T.sqEdge k) * dihedralClosedDerivSq T e k))
        = 2 * Real.sqrt (T.sqEdge k) *
            (∑ e : Fin 6, Real.sqrt (T.sqEdge e) * dihedralClosedDerivSq T e k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro e _
          ring
    _ = 2 * Real.sqrt (T.sqEdge k) * 0 := by
          rw [h]
    _ = 0 := by
          ring

/-- The theorem target left by the closed-form reduction. -/
def SchlaefliTetrahedronClosedFormTarget : Prop :=
  ∀ T : NonDegenerateTet, TetraSchlaefliClosedEquation T

/-- The six edge-coordinate closed-form Schläfli identities, stated after
the squared-edge algebraic reduction.  This is the finite algebraic core left
to prove. -/
def TetraSchlaefliSixEdgeClosedFormTarget : Prop :=
  ∀ T : NonDegenerateTet, ∀ k : Fin 6,
    (∑ e : Fin 6,
      Real.sqrt (T.sqEdge e) * dihedralClosedDerivSq T e k)
      = 0

/-- Polynomial-cofactor form of the six algebraic Schläfli identities. -/
def TetraSchlaefliSixEdgePolynomialTarget : Prop :=
  ∀ T : NonDegenerateTet, ∀ k : Fin 6,
    (∑ e : Fin 6,
      Real.sqrt (T.sqEdge e) * dihedralClosedDerivSqPoly T e k)
      = 0

/-- Rationalized Schläfli summand after using the cofactor discriminant to
remove the arccos radical.  Up to the common nonzero factor
`1 / sqrt (2 * cm3 a)`, the original polynomial-cofactor summand is this
pure rational expression. -/
def schlaefliPolySummandNorm (a : SqEdges) (e k : Fin 6) : ℝ :=
  match e with
  | 0 =>
      let P := CofactorPolynomial.cmCofactor3Poly 3 3 a
      let Q := CofactorPolynomial.cmCofactor3Poly 4 4 a
      let N := CofactorPolynomial.cmCofactor3Poly 3 4 a
      let Pp := CofactorPolynomial.cmCofactorPartial 3 3 k a
      let Qp := CofactorPolynomial.cmCofactorPartial 4 4 k a
      let Np := CofactorPolynomial.cmCofactorPartial 3 4 k a
      (-(2 * Np * P * Q - N * (Pp * Q + P * Qp))) / (2 * P * Q)
  | 1 =>
      let P := CofactorPolynomial.cmCofactor3Poly 2 2 a
      let Q := CofactorPolynomial.cmCofactor3Poly 4 4 a
      let N := CofactorPolynomial.cmCofactor3Poly 2 4 a
      let Pp := CofactorPolynomial.cmCofactorPartial 2 2 k a
      let Qp := CofactorPolynomial.cmCofactorPartial 4 4 k a
      let Np := CofactorPolynomial.cmCofactorPartial 2 4 k a
      (-(2 * Np * P * Q - N * (Pp * Q + P * Qp))) / (2 * P * Q)
  | 2 =>
      let P := CofactorPolynomial.cmCofactor3Poly 2 2 a
      let Q := CofactorPolynomial.cmCofactor3Poly 3 3 a
      let N := CofactorPolynomial.cmCofactor3Poly 2 3 a
      let Pp := CofactorPolynomial.cmCofactorPartial 2 2 k a
      let Qp := CofactorPolynomial.cmCofactorPartial 3 3 k a
      let Np := CofactorPolynomial.cmCofactorPartial 2 3 k a
      (-(2 * Np * P * Q - N * (Pp * Q + P * Qp))) / (2 * P * Q)
  | 3 =>
      let P := CofactorPolynomial.cmCofactor3Poly 1 1 a
      let Q := CofactorPolynomial.cmCofactor3Poly 4 4 a
      let N := CofactorPolynomial.cmCofactor3Poly 1 4 a
      let Pp := CofactorPolynomial.cmCofactorPartial 1 1 k a
      let Qp := CofactorPolynomial.cmCofactorPartial 4 4 k a
      let Np := CofactorPolynomial.cmCofactorPartial 1 4 k a
      (-(2 * Np * P * Q - N * (Pp * Q + P * Qp))) / (2 * P * Q)
  | 4 =>
      let P := CofactorPolynomial.cmCofactor3Poly 1 1 a
      let Q := CofactorPolynomial.cmCofactor3Poly 3 3 a
      let N := CofactorPolynomial.cmCofactor3Poly 1 3 a
      let Pp := CofactorPolynomial.cmCofactorPartial 1 1 k a
      let Qp := CofactorPolynomial.cmCofactorPartial 3 3 k a
      let Np := CofactorPolynomial.cmCofactorPartial 1 3 k a
      (-(2 * Np * P * Q - N * (Pp * Q + P * Qp))) / (2 * P * Q)
  | 5 =>
      let P := CofactorPolynomial.cmCofactor3Poly 1 1 a
      let Q := CofactorPolynomial.cmCofactor3Poly 2 2 a
      let N := CofactorPolynomial.cmCofactor3Poly 1 2 a
      let Pp := CofactorPolynomial.cmCofactorPartial 1 1 k a
      let Qp := CofactorPolynomial.cmCofactorPartial 2 2 k a
      let Np := CofactorPolynomial.cmCofactorPartial 1 2 k a
      (-(2 * Np * P * Q - N * (Pp * Q + P * Qp))) / (2 * P * Q)

/-- Numerator of the rationalized Schläfli summand. -/
def schlaefliPolySummandNum (a : SqEdges) (e k : Fin 6) : ℝ :=
  let p := DihedralCayleyMenger.oppositeCMVertices e |>.1
  let q := DihedralCayleyMenger.oppositeCMVertices e |>.2
  let P := CofactorPolynomial.cmCofactor3Poly p p a
  let Q := CofactorPolynomial.cmCofactor3Poly q q a
  let N := CofactorPolynomial.cmCofactor3Poly p q a
  let Pp := CofactorPolynomial.cmCofactorPartial p p k a
  let Qp := CofactorPolynomial.cmCofactorPartial q q k a
  let Np := CofactorPolynomial.cmCofactorPartial p q k a
  (-(2 * Np * P * Q - N * (Pp * Q + P * Qp)))

/-- Denominator of the rationalized Schläfli summand. -/
def schlaefliPolySummandDen (a : SqEdges) (e : Fin 6) : ℝ :=
  let p := DihedralCayleyMenger.oppositeCMVertices e |>.1
  let q := DihedralCayleyMenger.oppositeCMVertices e |>.2
  2 * CofactorPolynomial.cmCofactor3Poly p p a *
    CofactorPolynomial.cmCofactor3Poly q q a

/-- The normalized summand is numerator divided by denominator. -/
theorem schlaefliPolySummandNorm_eq_num_div_den
    (a : SqEdges) (e k : Fin 6) :
    schlaefliPolySummandNorm a e k =
      schlaefliPolySummandNum a e k / schlaefliPolySummandDen a e := by
  fin_cases e <;>
    simp [schlaefliPolySummandNorm, schlaefliPolySummandNum,
      schlaefliPolySummandDen, DihedralCayleyMenger.oppositeCMVertices]

/-- Product denominator for clearing the six rational Schläfli summands. -/
def schlaefliCommonDenom (a : SqEdges) : ℝ :=
  ∏ e : Fin 6, schlaefliPolySummandDen a e

/-- Common numerator after clearing all six rational Schläfli summands. -/
def schlaefliCommonNumerator (a : SqEdges) (k : Fin 6) : ℝ :=
  ∑ e : Fin 6,
    schlaefliPolySummandNum a e k *
      ∏ j ∈ (Finset.univ.erase e), schlaefliPolySummandDen a j

/-- Each rationalized Schläfli summand denominator is nonzero on a
nondegenerate tetrahedron. -/
theorem schlaefliPolySummandDen_ne_zero
    (T : NonDegenerateTet) (e : Fin 6) :
    schlaefliPolySummandDen T.sqEdge e ≠ 0 := by
  unfold schlaefliPolySummandDen
  have hprod := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T e
  fin_cases e <;>
    simpa [DihedralCayleyMenger.oppositeCMVertices,
      CofactorDerivatives.dihedralCofactorProductPoly, mul_assoc] using
      mul_ne_zero two_ne_zero hprod

/-- The common denominator is nonzero on a nondegenerate tetrahedron. -/
theorem schlaefliCommonDenom_ne_zero
    (T : NonDegenerateTet) :
    schlaefliCommonDenom T.sqEdge ≠ 0 := by
  unfold schlaefliCommonDenom
  exact Finset.prod_ne_zero_iff.mpr (by
    intro e _
    exact schlaefliPolySummandDen_ne_zero T e)

/-- Remaining common-numerator closure target.  The intended proof is six
coordinate-specific numerator lemmas rather than one global unfold. -/
def SchlaefliCommonNumeratorTarget : Prop :=
  ∀ a : SqEdges, ∀ k : Fin 6, schlaefliCommonNumerator a k = 0

/-- The rationalized six-edge Schläfli identities.  This is the remaining
post-radical-normalization target: prove these six rational sums by expanding
`schlaefliPolySummandNorm`, clearing the cofactor-product denominators, and
finishing with `ring_nf`. -/
def SchlaefliPolySummandNormSumTarget : Prop :=
  ∀ T : NonDegenerateTet, ∀ k : Fin 6,
    (∑ e : Fin 6, schlaefliPolySummandNorm T.sqEdge e k) = 0

/-- Explicit expansion of a six-term finite sum over `Fin 6`. -/
theorem sum_fin6_real (f : Fin 6 → ℝ) :
    (∑ e : Fin 6, f e) =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  norm_num [Fin.sum_univ_succ]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5
  ring

/- The next closure step is to prove the six coordinate instances of
`SchlaefliPolySummandNormSumTarget`.  Direct global unfolding still creates
large inverse-normalized goals, so the intended implementation is one
coordinate numerator lemma at a time. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
/-- The rationalized six-edge Schläfli sums vanish. -/
theorem schlaefliPolySummandNorm_sum_eq_zero :
    SchlaefliPolySummandNormSumTarget := by
  intro T k
  rw [sum_fin6_real]
  have h0p := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 0
  have h1p := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 1
  have h5p := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 5
  simp [CofactorDerivatives.dihedralCofactorProductPoly,
    DihedralCayleyMenger.oppositeCMVertices] at h0p h1p h5p
  have h33 : CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge ≠ 0 := h0p.1
  have h44 : CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge ≠ 0 := h0p.2
  have h22 : CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge ≠ 0 := h1p.1
  have h11 : CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge ≠ 0 := h5p.1
  let D : ℝ :=
    CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
      CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge *
      CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge *
      CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge
  have hD : D ≠ 0 := by
    unfold D
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h11 h22) h33) h44
  have hmul :
      D * (schlaefliPolySummandNorm T.sqEdge 0 k +
          schlaefliPolySummandNorm T.sqEdge 1 k +
          schlaefliPolySummandNorm T.sqEdge 2 k +
          schlaefliPolySummandNorm T.sqEdge 3 k +
          schlaefliPolySummandNorm T.sqEdge 4 k +
          schlaefliPolySummandNorm T.sqEdge 5 k) = 0 := by
    fin_cases k <;>
      unfold D schlaefliPolySummandNorm <;>
      field_simp [h11, h22, h33, h44] <;>
      simp [CofactorPolynomial.cmCofactor3Poly, CofactorPolynomial.cmCofactorPartial] <;>
      ring_nf
  exact (mul_eq_zero.mp hmul).resolve_left hD

/-- Remaining bridge target: each polynomial-cofactor Schläfli summand should
equal the rationalized summand times the common factor
`1 / sqrt (2 * cm3)`.  The normalized rational sum is already proved; this
bridge is the last radical-cancellation step before
`TetraSchlaefliSixEdgePolynomialTarget`. -/
def SchlaefliSummandBridgeTarget : Prop :=
  ∀ T : NonDegenerateTet, ∀ e k : Fin 6,
    Real.sqrt (T.sqEdge e) * dihedralClosedDerivSqPoly T e k =
      (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
        schlaefliPolySummandNorm T.sqEdge e k

set_option maxHeartbeats 4000000
/-- Radical bridge for edge `0`. -/
theorem schlaefli_summand_bridge_edge0
    (T : NonDegenerateTet) (k : Fin 6) :
    Real.sqrt (T.sqEdge 0) * dihedralClosedDerivSqPoly T 0 k =
      (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
        schlaefliPolySummandNorm T.sqEdge 0 k := by
  unfold dihedralClosedDerivSqPoly
  have hp_nonneg := CofactorDerivatives.dihedralCofactorProductPoly_nonneg_of_nonDegenerate T 0
  have hp_exp : 0 ≤
      CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_nonneg
  have hp_ne := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 0
  have hp_exp_ne :
      CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge ≠ 0 := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_ne
  have h33 : CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).1
  have h44 : CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).2
  have hd_ne := CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T 0
  have hnum_nonneg : 0 ≤ 2 * cm3 T.sqEdge * T.sqEdge 0 := by
    nlinarith [T.cm_pos, T.sqEdge_pos 0]
  rw [CofactorDerivatives.sqrt_one_sub_dihedralCos3SqPoly_sq_eq
    T.sqEdge 0 hp_nonneg hp_ne hd_ne hnum_nonneg]
  have hsqrt : Real.sqrt (2 * cm3 T.sqEdge * T.sqEdge 0) =
      Real.sqrt (2 * cm3 T.sqEdge) * Real.sqrt (T.sqEdge 0) := by
    have hleft : 0 ≤ 2 * cm3 T.sqEdge := by nlinarith [T.cm_pos]
    rw [show 2 * cm3 T.sqEdge * T.sqEdge 0 =
        (2 * cm3 T.sqEdge) * T.sqEdge 0 by ring]
    rw [Real.sqrt_mul hleft]
  rw [hsqrt]
  simp [CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv,
    CofactorDerivatives.dihedralDenom3PolyClosedDerivValue,
    CofactorDerivatives.dihedralDenom3Poly,
    DihedralCayleyMenger.oppositeCMVertices,
    schlaefliPolySummandNorm]
  have hcm : Real.sqrt (2 * cm3 T.sqEdge) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [T.cm_pos] : 0 < 2 * cm3 T.sqEdge)
  have he : Real.sqrt (T.sqEdge 0) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (T.sqEdge_pos 0)
  have hd :
      Real.sqrt (CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge) ≠ 0 := by
    simpa [CofactorDerivatives.dihedralDenom3Poly,
      DihedralCayleyMenger.oppositeCMVertices] using hd_ne
  field_simp [hcm, he, hd]
  rw [Real.sq_sqrt hp_exp]
  field_simp [hcm, h33, h44]
  fin_cases k <;>
    simp [CofactorPolynomial.cmCofactor3Poly,
      CofactorPolynomial.cmCofactorPartial] <;>
    ring_nf


/-- Radical bridge for edge `1`. -/
theorem schlaefli_summand_bridge_edge1
    (T : NonDegenerateTet) (k : Fin 6) :
    Real.sqrt (T.sqEdge 1) * dihedralClosedDerivSqPoly T 1 k =
      (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
        schlaefliPolySummandNorm T.sqEdge 1 k := by
  unfold dihedralClosedDerivSqPoly
  have hp_nonneg := CofactorDerivatives.dihedralCofactorProductPoly_nonneg_of_nonDegenerate T 1
  have hp_exp : 0 ≤
      CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_nonneg
  have hp_ne := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 1
  have hp_exp_ne :
      CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge ≠ 0 := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_ne
  have hp_left : CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).1
  have hp_right : CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).2
  have hd_ne := CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T 1
  have hnum_nonneg : 0 ≤ 2 * cm3 T.sqEdge * T.sqEdge 1 := by
    nlinarith [T.cm_pos, T.sqEdge_pos 1]
  rw [CofactorDerivatives.sqrt_one_sub_dihedralCos3SqPoly_sq_eq
    T.sqEdge 1 hp_nonneg hp_ne hd_ne hnum_nonneg]
  have hsqrt : Real.sqrt (2 * cm3 T.sqEdge * T.sqEdge 1) =
      Real.sqrt (2 * cm3 T.sqEdge) * Real.sqrt (T.sqEdge 1) := by
    have hleft : 0 ≤ 2 * cm3 T.sqEdge := by nlinarith [T.cm_pos]
    rw [show 2 * cm3 T.sqEdge * T.sqEdge 1 =
        (2 * cm3 T.sqEdge) * T.sqEdge 1 by ring]
    rw [Real.sqrt_mul hleft]
  rw [hsqrt]
  simp [CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv,
    CofactorDerivatives.dihedralDenom3PolyClosedDerivValue,
    CofactorDerivatives.dihedralDenom3Poly,
    DihedralCayleyMenger.oppositeCMVertices,
    schlaefliPolySummandNorm]
  have hcm : Real.sqrt (2 * cm3 T.sqEdge) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [T.cm_pos] : 0 < 2 * cm3 T.sqEdge)
  have he : Real.sqrt (T.sqEdge 1) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (T.sqEdge_pos 1)
  have hd :
      Real.sqrt (CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge) ≠ 0 := by
    simpa [CofactorDerivatives.dihedralDenom3Poly,
      DihedralCayleyMenger.oppositeCMVertices] using hd_ne
  field_simp [hcm, he, hd]
  rw [Real.sq_sqrt hp_exp]
  field_simp [hcm, hp_left, hp_right]
  fin_cases k <;>
    simp [CofactorPolynomial.cmCofactor3Poly,
      CofactorPolynomial.cmCofactorPartial] <;>
    ring_nf

/-- Radical bridge for edge `2`. -/
theorem schlaefli_summand_bridge_edge2
    (T : NonDegenerateTet) (k : Fin 6) :
    Real.sqrt (T.sqEdge 2) * dihedralClosedDerivSqPoly T 2 k =
      (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
        schlaefliPolySummandNorm T.sqEdge 2 k := by
  unfold dihedralClosedDerivSqPoly
  have hp_nonneg := CofactorDerivatives.dihedralCofactorProductPoly_nonneg_of_nonDegenerate T 2
  have hp_exp : 0 ≤
      CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_nonneg
  have hp_ne := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 2
  have hp_exp_ne :
      CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge ≠ 0 := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_ne
  have hp_left : CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).1
  have hp_right : CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).2
  have hd_ne := CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T 2
  have hnum_nonneg : 0 ≤ 2 * cm3 T.sqEdge * T.sqEdge 2 := by
    nlinarith [T.cm_pos, T.sqEdge_pos 2]
  rw [CofactorDerivatives.sqrt_one_sub_dihedralCos3SqPoly_sq_eq
    T.sqEdge 2 hp_nonneg hp_ne hd_ne hnum_nonneg]
  have hsqrt : Real.sqrt (2 * cm3 T.sqEdge * T.sqEdge 2) =
      Real.sqrt (2 * cm3 T.sqEdge) * Real.sqrt (T.sqEdge 2) := by
    have hleft : 0 ≤ 2 * cm3 T.sqEdge := by nlinarith [T.cm_pos]
    rw [show 2 * cm3 T.sqEdge * T.sqEdge 2 =
        (2 * cm3 T.sqEdge) * T.sqEdge 2 by ring]
    rw [Real.sqrt_mul hleft]
  rw [hsqrt]
  simp [CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv,
    CofactorDerivatives.dihedralDenom3PolyClosedDerivValue,
    CofactorDerivatives.dihedralDenom3Poly,
    DihedralCayleyMenger.oppositeCMVertices,
    schlaefliPolySummandNorm]
  have hcm : Real.sqrt (2 * cm3 T.sqEdge) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [T.cm_pos] : 0 < 2 * cm3 T.sqEdge)
  have he : Real.sqrt (T.sqEdge 2) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (T.sqEdge_pos 2)
  have hd :
      Real.sqrt (CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge) ≠ 0 := by
    simpa [CofactorDerivatives.dihedralDenom3Poly,
      DihedralCayleyMenger.oppositeCMVertices] using hd_ne
  field_simp [hcm, he, hd]
  rw [Real.sq_sqrt hp_exp]
  field_simp [hcm, hp_left, hp_right]
  fin_cases k <;>
    simp [CofactorPolynomial.cmCofactor3Poly,
      CofactorPolynomial.cmCofactorPartial] <;>
    ring_nf

/-- Radical bridge for edge `3`. -/
theorem schlaefli_summand_bridge_edge3
    (T : NonDegenerateTet) (k : Fin 6) :
    Real.sqrt (T.sqEdge 3) * dihedralClosedDerivSqPoly T 3 k =
      (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
        schlaefliPolySummandNorm T.sqEdge 3 k := by
  unfold dihedralClosedDerivSqPoly
  have hp_nonneg := CofactorDerivatives.dihedralCofactorProductPoly_nonneg_of_nonDegenerate T 3
  have hp_exp : 0 ≤
      CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_nonneg
  have hp_ne := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 3
  have hp_exp_ne :
      CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge ≠ 0 := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_ne
  have hp_left : CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).1
  have hp_right : CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).2
  have hd_ne := CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T 3
  have hnum_nonneg : 0 ≤ 2 * cm3 T.sqEdge * T.sqEdge 3 := by
    nlinarith [T.cm_pos, T.sqEdge_pos 3]
  rw [CofactorDerivatives.sqrt_one_sub_dihedralCos3SqPoly_sq_eq
    T.sqEdge 3 hp_nonneg hp_ne hd_ne hnum_nonneg]
  have hsqrt : Real.sqrt (2 * cm3 T.sqEdge * T.sqEdge 3) =
      Real.sqrt (2 * cm3 T.sqEdge) * Real.sqrt (T.sqEdge 3) := by
    have hleft : 0 ≤ 2 * cm3 T.sqEdge := by nlinarith [T.cm_pos]
    rw [show 2 * cm3 T.sqEdge * T.sqEdge 3 =
        (2 * cm3 T.sqEdge) * T.sqEdge 3 by ring]
    rw [Real.sqrt_mul hleft]
  rw [hsqrt]
  simp [CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv,
    CofactorDerivatives.dihedralDenom3PolyClosedDerivValue,
    CofactorDerivatives.dihedralDenom3Poly,
    DihedralCayleyMenger.oppositeCMVertices,
    schlaefliPolySummandNorm]
  have hcm : Real.sqrt (2 * cm3 T.sqEdge) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [T.cm_pos] : 0 < 2 * cm3 T.sqEdge)
  have he : Real.sqrt (T.sqEdge 3) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (T.sqEdge_pos 3)
  have hd :
      Real.sqrt (CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 4 4 T.sqEdge) ≠ 0 := by
    simpa [CofactorDerivatives.dihedralDenom3Poly,
      DihedralCayleyMenger.oppositeCMVertices] using hd_ne
  field_simp [hcm, he, hd]
  rw [Real.sq_sqrt hp_exp]
  field_simp [hcm, hp_left, hp_right]
  fin_cases k <;>
    simp [CofactorPolynomial.cmCofactor3Poly,
      CofactorPolynomial.cmCofactorPartial] <;>
    ring_nf

/-- Radical bridge for edge `4`. -/
theorem schlaefli_summand_bridge_edge4
    (T : NonDegenerateTet) (k : Fin 6) :
    Real.sqrt (T.sqEdge 4) * dihedralClosedDerivSqPoly T 4 k =
      (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
        schlaefliPolySummandNorm T.sqEdge 4 k := by
  unfold dihedralClosedDerivSqPoly
  have hp_nonneg := CofactorDerivatives.dihedralCofactorProductPoly_nonneg_of_nonDegenerate T 4
  have hp_exp : 0 ≤
      CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_nonneg
  have hp_ne := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 4
  have hp_exp_ne :
      CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge ≠ 0 := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_ne
  have hp_left : CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).1
  have hp_right : CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).2
  have hd_ne := CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T 4
  have hnum_nonneg : 0 ≤ 2 * cm3 T.sqEdge * T.sqEdge 4 := by
    nlinarith [T.cm_pos, T.sqEdge_pos 4]
  rw [CofactorDerivatives.sqrt_one_sub_dihedralCos3SqPoly_sq_eq
    T.sqEdge 4 hp_nonneg hp_ne hd_ne hnum_nonneg]
  have hsqrt : Real.sqrt (2 * cm3 T.sqEdge * T.sqEdge 4) =
      Real.sqrt (2 * cm3 T.sqEdge) * Real.sqrt (T.sqEdge 4) := by
    have hleft : 0 ≤ 2 * cm3 T.sqEdge := by nlinarith [T.cm_pos]
    rw [show 2 * cm3 T.sqEdge * T.sqEdge 4 =
        (2 * cm3 T.sqEdge) * T.sqEdge 4 by ring]
    rw [Real.sqrt_mul hleft]
  rw [hsqrt]
  simp [CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv,
    CofactorDerivatives.dihedralDenom3PolyClosedDerivValue,
    CofactorDerivatives.dihedralDenom3Poly,
    DihedralCayleyMenger.oppositeCMVertices,
    schlaefliPolySummandNorm]
  have hcm : Real.sqrt (2 * cm3 T.sqEdge) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [T.cm_pos] : 0 < 2 * cm3 T.sqEdge)
  have he : Real.sqrt (T.sqEdge 4) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (T.sqEdge_pos 4)
  have hd :
      Real.sqrt (CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 3 3 T.sqEdge) ≠ 0 := by
    simpa [CofactorDerivatives.dihedralDenom3Poly,
      DihedralCayleyMenger.oppositeCMVertices] using hd_ne
  field_simp [hcm, he, hd]
  rw [Real.sq_sqrt hp_exp]
  field_simp [hcm, hp_left, hp_right]
  fin_cases k <;>
    simp [CofactorPolynomial.cmCofactor3Poly,
      CofactorPolynomial.cmCofactorPartial] <;>
    ring_nf

/-- Radical bridge for edge `5`. -/
theorem schlaefli_summand_bridge_edge5
    (T : NonDegenerateTet) (k : Fin 6) :
    Real.sqrt (T.sqEdge 5) * dihedralClosedDerivSqPoly T 5 k =
      (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
        schlaefliPolySummandNorm T.sqEdge 5 k := by
  unfold dihedralClosedDerivSqPoly
  have hp_nonneg := CofactorDerivatives.dihedralCofactorProductPoly_nonneg_of_nonDegenerate T 5
  have hp_exp : 0 ≤
      CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_nonneg
  have hp_ne := CofactorDerivatives.dihedralCofactorProductPoly_ne_zero_of_nonDegenerate T 5
  have hp_exp_ne :
      CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge ≠ 0 := by
    simpa [CofactorDerivatives.dihedralCofactorProductPoly,
      DihedralCayleyMenger.oppositeCMVertices] using hp_ne
  have hp_left : CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).1
  have hp_right : CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge ≠ 0 :=
    (mul_ne_zero_iff.mp hp_exp_ne).2
  have hd_ne := CofactorDerivatives.dihedralDenom3Poly_ne_zero_of_nonDegenerate T 5
  have hnum_nonneg : 0 ≤ 2 * cm3 T.sqEdge * T.sqEdge 5 := by
    nlinarith [T.cm_pos, T.sqEdge_pos 5]
  rw [CofactorDerivatives.sqrt_one_sub_dihedralCos3SqPoly_sq_eq
    T.sqEdge 5 hp_nonneg hp_ne hd_ne hnum_nonneg]
  have hsqrt : Real.sqrt (2 * cm3 T.sqEdge * T.sqEdge 5) =
      Real.sqrt (2 * cm3 T.sqEdge) * Real.sqrt (T.sqEdge 5) := by
    have hleft : 0 ≤ 2 * cm3 T.sqEdge := by nlinarith [T.cm_pos]
    rw [show 2 * cm3 T.sqEdge * T.sqEdge 5 =
        (2 * cm3 T.sqEdge) * T.sqEdge 5 by ring]
    rw [Real.sqrt_mul hleft]
  rw [hsqrt]
  simp [CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv,
    CofactorDerivatives.dihedralDenom3PolyClosedDerivValue,
    CofactorDerivatives.dihedralDenom3Poly,
    DihedralCayleyMenger.oppositeCMVertices,
    schlaefliPolySummandNorm]
  have hcm : Real.sqrt (2 * cm3 T.sqEdge) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (by nlinarith [T.cm_pos] : 0 < 2 * cm3 T.sqEdge)
  have he : Real.sqrt (T.sqEdge 5) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (T.sqEdge_pos 5)
  have hd :
      Real.sqrt (CofactorPolynomial.cmCofactor3Poly 1 1 T.sqEdge *
        CofactorPolynomial.cmCofactor3Poly 2 2 T.sqEdge) ≠ 0 := by
    simpa [CofactorDerivatives.dihedralDenom3Poly,
      DihedralCayleyMenger.oppositeCMVertices] using hd_ne
  field_simp [hcm, he, hd]
  rw [Real.sq_sqrt hp_exp]
  field_simp [hcm, hp_left, hp_right]
  fin_cases k <;>
    simp [CofactorPolynomial.cmCofactor3Poly,
      CofactorPolynomial.cmCofactorPartial] <;>
    ring_nf

/-- The radical bridge from the original polynomial-cofactor summand to the
rationalized summand. -/
theorem schlaefliSummandBridge :
    SchlaefliSummandBridgeTarget := by
  intro T e k
  fin_cases e
  · exact schlaefli_summand_bridge_edge0 T k
  · exact schlaefli_summand_bridge_edge1 T k
  · exact schlaefli_summand_bridge_edge2 T k
  · exact schlaefli_summand_bridge_edge3 T k
  · exact schlaefli_summand_bridge_edge4 T k
  · exact schlaefli_summand_bridge_edge5 T k

/-- The corrected six-edge polynomial-cofactor Schläfli identity. -/
theorem tetraSchlaefliSixEdgePolynomial :
    TetraSchlaefliSixEdgePolynomialTarget := by
  intro T k
  calc
    (∑ e : Fin 6, Real.sqrt (T.sqEdge e) * dihedralClosedDerivSqPoly T e k)
        = ∑ e : Fin 6,
            (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
              schlaefliPolySummandNorm T.sqEdge e k := by
          refine Finset.sum_congr rfl ?_
          intro e _
          exact schlaefliSummandBridge T e k
    _ = (1 / Real.sqrt (2 * cm3 T.sqEdge)) *
          (∑ e : Fin 6, schlaefliPolySummandNorm T.sqEdge e k) := by
          exact (Finset.mul_sum _ _ _).symm
    _ = 0 := by
          rw [schlaefliPolySummandNorm_sum_eq_zero T k]
          ring

/-- The polynomial-cofactor target implies the determinant-cofactor target. -/
theorem sixEdgeClosedForm_of_polynomial
    (hPoly : TetraSchlaefliSixEdgePolynomialTarget) :
    TetraSchlaefliSixEdgeClosedFormTarget := by
  intro T k
  calc
    (∑ e : Fin 6, Real.sqrt (T.sqEdge e) * dihedralClosedDerivSq T e k)
        = ∑ e : Fin 6, Real.sqrt (T.sqEdge e) * dihedralClosedDerivSqPoly T e k := by
          refine Finset.sum_congr rfl ?_
          intro e _
          rw [dihedralClosedDerivSq_eq_poly]
    _ = 0 := hPoly T k

/-- The six explicit squared-edge identities imply the full corrected
edge-length closed-form Schläfli theorem. -/
theorem schlaefliClosedForm_of_sixEdgeSq
    (hSix : TetraSchlaefliSixEdgeClosedFormTarget) :
    SchlaefliTetrahedronClosedFormTarget := by
  intro T
  apply TetraSchlaefliClosedEquation_of_sq
  intro k
  exact hSix T k

/-- The six explicit algebraic edge identities discharge the local
tetrahedral Schläfli data package. -/
theorem schlaefliTetrahedronTheorem_of_sixEdgeSq
    (hSix : TetraSchlaefliSixEdgeClosedFormTarget) :
    SchlaefliTetrahedronTheorem := by
  intro T
  exact ⟨tetraSchlaefliDerivativeData_of_equation T
    (fun e k => dihedralClosedDerivLength T e k)
    (fun k => volume3ClosedDerivLength T k)
    ((schlaefliClosedForm_of_sixEdgeSq hSix) T)⟩

/-- Once the closed-form equation is proved, it constructs the local
Schläfli derivative package with no caller-supplied data. -/
def tetraSchlaefliDerivativeData_closedForm
    (T : NonDegenerateTet) (hT : TetraSchlaefliClosedEquation T) :
    TetraSchlaefliDerivativeData T :=
  tetraSchlaefliDerivativeData_of_equation T
    (fun e k => dihedralClosedDerivLength T e k)
    (fun k => volume3ClosedDerivLength T k)
    hT

/-- A closed-form Schläfli proof discharges the existing tetrahedral
Schläfli theorem target. -/
theorem schlaefliTetrahedronTheorem_of_closedForm
    (h : SchlaefliTetrahedronClosedFormTarget) :
    SchlaefliTetrahedronTheorem := by
  intro T
  exact ⟨tetraSchlaefliDerivativeData_closedForm T (h T)⟩

/-- Determinant-cofactor six-edge Schläfli identity. -/
theorem tetraSchlaefliSixEdgeClosedForm :
    TetraSchlaefliSixEdgeClosedFormTarget :=
  sixEdgeClosedForm_of_polynomial tetraSchlaefliSixEdgePolynomial

/-- Closed-form tetrahedral Schläfli theorem. -/
theorem schlaefliTetrahedronClosedForm :
    SchlaefliTetrahedronClosedFormTarget :=
  schlaefliClosedForm_of_sixEdgeSq tetraSchlaefliSixEdgeClosedForm

/-- The local tetrahedral Schläfli derivative-data package is now constructed
from the explicit cofactor formulas. -/
theorem schlaefliTetrahedronTheorem :
    SchlaefliTetrahedronTheorem :=
  schlaefliTetrahedronTheorem_of_closedForm schlaefliTetrahedronClosedForm

/-- Realized tetrahedra with strict face-normal independence inherit the
same closed-form Schläfli package once the polynomial identity is proved. -/
def RealizedNonDegenerateTet.schlaefliData_of_closedForm
    (T : RealizedNonDegenerateTet)
    (h : TetraSchlaefliClosedEquation T.tet) :
    TetraSchlaefliDerivativeData T.tet :=
  tetraSchlaefliDerivativeData_closedForm T.tet h

end

end SchlaefliTetrahedronProof
end Geometry
end IndisputableMonolith

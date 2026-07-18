import IndisputableMonolith.Gravity.Analysis.ReggeTTBlochInterfaceAudit

/-!
# Regge TT bucket-fiber aggregation (Gate C-A2f)

QG full-theory campaign, Paper C / Pillar 1, Lane C of the finishing
charter.  This module closes the bucket-fiber aggregation gate left OPEN by
`ReggeTTBlochInterfaceAudit`: the radical-bearing raw stencil coefficient
`J_fg / (2 * sqrt a*_f)` (with `J = flatAngleJacobian` the flat angle
Jacobian and `a* = freudenthalTetSqEdges` the flat tuple) equals a literal
rational table on EVERY bucket, all 36 slot pairs, not just the row-0 smoke
bucket and the worst radical entry already kernel-recorded there.

## Anti-tautology structure (binding)

* `rationalStencilWeight` below is an INDEPENDENT literal table: a bare
  36-branch match on the bucket's slot pair with literal rational values.
  It is NOT defined as any fiber sum, radical expression, or alias of
  `rawJacobianCoefficient`; the two sides of the headline are independently
  defined objects.
* The headline `aggregate_raw_weight_eq_rational` proves, for EVERY bucket
  `b` (all slot pairs, all integer phase keys), that the actual
  radical-bearing coefficient `rawJacobianCoefficient b.left b.right`
  (defined in the interface audit from `flatAngleJacobian` and
  `freudenthalTetSqEdges`, both of which come from the kernel-proved A2/A3
  derivative machinery) equals the real cast of the table entry.
* The proof route is the proved Schlaefli radical bridge
  (`schlaefli_summand_bridge_edge0..5`, packaged as
  `schlaefliSummandBridge`): `sqrt(a*_f) * (dtheta_f/da_g) =
  (1/sqrt(2*cm3)) * schlaefliPolySummandNorm`, with `sqrt(2*cm3) = 4` at
  the flat tuple, so every entry is a RADICAL-FREE rational cofactor
  expression divided by `8 * a*_f`.  Each of the 36 entries is then closed
  by kernel rational arithmetic.  No numerics, no `native_decide`.

## Value set

The proved table takes values in `{0, 1/12, +-1/8, +-1/4}`.  The panel
preregistration expected `{0, +-1/4, -1/8}`; the kernel value set is the
strictly larger list above (row 1 diagonal carries `+1/8`, row 2 diagonal
carries `+1/12`, row 4 diagonal carries `+1/8`).  The two entries the
interface audit already recorded (`(0,5) = 1/4` smoke, `(1,2) = -1/8`
worst radical) are reproduced exactly, as corollaries of the headline.

## Inherited axiom footprint (disclosure)

Everything here is pure algebra over the derivative-gate chain; the
expected footprint of every theorem in this file is the standard trio
`[propext, Classical.choice, Quot.sound]`.  `#print axioms` receipts are
emitted at the end of the file.

No `sorry`, no `admit`, no new axioms, no `native_decide`, no `: True` or
`Nonempty`-only headline in this file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTBucketAggregation

open Geometry.FreudenthalCubeTriangulation (freudenthalTetSqEdges freudenthalTet)
open ReggeTTBlochInterfaceAudit (Bucket rawJacobianCoefficient row0SmokeBucket
  worstRadicalBucket)

noncomputable section

/-! ## §1. The independent literal rational table -/

/-- THE FULL LITERAL RATIONAL TABLE (all 36 slot pairs).  This is an
independent literal table in the sense demanded by the panel: a bare match
with literal rational values, phase-independent, never defined through any
fiber sum or through `rawJacobianCoefficient`.  Derived offline from the
closed forms of `flatAngleJacobian` and `freudenthalTetSqEdges` and then
kernel-verified entry by entry in `aggregate_raw_weight_eq_rational`. -/
def rationalStencilWeight (b : Bucket) : ℚ :=
  match b.left, b.right with
  | 0, 0 => 0        | 0, 1 => 0        | 0, 2 => 0
  | 0, 3 => 0        | 0, 4 => -(1 / 8) | 0, 5 => 1 / 4
  | 1, 0 => 0        | 1, 1 => 1 / 8    | 1, 2 => -(1 / 8)
  | 1, 3 => -(1 / 4) | 1, 4 => 1 / 4    | 1, 5 => -(1 / 8)
  | 2, 0 => 0        | 2, 1 => -(1 / 8) | 2, 2 => 1 / 12
  | 2, 3 => 1 / 4    | 2, 4 => -(1 / 8) | 2, 5 => 0
  | 3, 0 => 0        | 3, 1 => -(1 / 4) | 3, 2 => 1 / 4
  | 3, 3 => 1 / 4    | 3, 4 => -(1 / 4) | 3, 5 => 0
  | 4, 0 => -(1 / 8) | 4, 1 => 1 / 4    | 4, 2 => -(1 / 8)
  | 4, 3 => -(1 / 4) | 4, 4 => 1 / 8    | 4, 5 => 0
  | 5, 0 => 1 / 4    | 5, 1 => -(1 / 8) | 5, 2 => 0
  | 5, 3 => 0        | 5, 4 => 0        | 5, 5 => 0

/-! ## §2. The radical-free normal form of every raw coefficient -/

/-- Every raw coefficient is the rationalized Schlaefli summand divided by
`8 * a*_f`: `J_fg / (2 * sqrt a*_f) = schlaefliPolySummandNorm(a*, f, g) /
(8 * a*_f)`.  Route: the proved radical bridge
`sqrt(a_f) * (dtheta_f/da_g) = (1/sqrt(2*cm3)) * norm` with
`sqrt(2 * cm3 a*) = sqrt 16 = 4` at the flat tuple, then
`sqrt(a_f) * sqrt(a_f) = a_f`.  No radical survives on the right. -/
theorem rawJacobianCoefficient_eq_norm_div (f g : Fin 6) :
    rawJacobianCoefficient f g =
      Geometry.SchlaefliTetrahedronProof.schlaefliPolySummandNorm
          freudenthalTetSqEdges f g /
        (8 * freudenthalTetSqEdges f) := by
  have hb := Geometry.SchlaefliTetrahedronProof.schlaefliSummandBridge
    freudenthalTet f g
  have h4 : Real.sqrt (2 * Geometry.CayleyMengerPolynomial.cm3
      freudenthalTet.sqEdge) = 4 := by
    have hcm : Geometry.CayleyMengerPolynomial.cm3 freudenthalTet.sqEdge = 8 :=
      Geometry.FreudenthalCubeTriangulation.cm3_freudenthalTetSqEdges
    rw [hcm, show (2 : ℝ) * 8 = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  rw [h4] at hb
  have hJ : ReggeTTDerivativeGate.flatAngleJacobian f g =
      Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSqPoly
        freudenthalTet f g := by
    rw [ReggeTTDerivativeGate.flatAngleJacobian_eq_dihedralClosedDerivSq]
    exact Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSq_eq_poly
      freudenthalTet f g
  have hpos : (0 : ℝ) < freudenthalTetSqEdges f := freudenthalTet.sqEdge_pos f
  have hsqrt_ne : Real.sqrt (freudenthalTetSqEdges f) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hsq : Real.sqrt (freudenthalTetSqEdges f) *
      Real.sqrt (freudenthalTetSqEdges f) = freudenthalTetSqEdges f :=
    Real.mul_self_sqrt hpos.le
  unfold rawJacobianCoefficient
  rw [hJ]
  rw [show freudenthalTet.sqEdge = freudenthalTetSqEdges from rfl] at hb
  rw [div_eq_div_iff
    (by positivity : (2 : ℝ) * Real.sqrt (freudenthalTetSqEdges f) ≠ 0)
    (by positivity : (8 : ℝ) * freudenthalTetSqEdges f ≠ 0)]
  calc
    Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSqPoly
          freudenthalTet f g * (8 * freudenthalTetSqEdges f)
        = 8 * (Real.sqrt (freudenthalTetSqEdges f) *
            Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSqPoly
              freudenthalTet f g) * Real.sqrt (freudenthalTetSqEdges f) := by
          rw [show Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSqPoly
                freudenthalTet f g * (8 * freudenthalTetSqEdges f) =
              8 * (Geometry.SchlaefliTetrahedronProof.dihedralClosedDerivSqPoly
                freudenthalTet f g *
                (Real.sqrt (freudenthalTetSqEdges f) *
                  Real.sqrt (freudenthalTetSqEdges f))) by rw [hsq]; ring]
          ring
    _ = 8 * (1 / 4 *
          Geometry.SchlaefliTetrahedronProof.schlaefliPolySummandNorm
            freudenthalTetSqEdges f g) * Real.sqrt (freudenthalTetSqEdges f) := by
          rw [hb]
    _ = Geometry.SchlaefliTetrahedronProof.schlaefliPolySummandNorm
          freudenthalTetSqEdges f g *
            (2 * Real.sqrt (freudenthalTetSqEdges f)) := by
          ring

/-- All 36 raw coefficients evaluated to exact rationals.  Each entry is
the radical-free normal form of `rawJacobianCoefficient_eq_norm_div`
evaluated by kernel rational arithmetic on the flat integer tuple. -/
theorem rawJacobianCoefficient_eval (f g : Fin 6) :
    rawJacobianCoefficient f g =
      ((rationalStencilWeight ⟨f, g, fun _ => 0⟩ : ℚ) : ℝ) := by
  rw [rawJacobianCoefficient_eq_norm_div]
  fin_cases f <;> fin_cases g <;>
    norm_num [rationalStencilWeight,
      Geometry.SchlaefliTetrahedronProof.schlaefliPolySummandNorm,
      Geometry.CofactorPolynomial.cmCofactor3Poly,
      Geometry.CofactorPolynomial.cmCofactorPartial,
      freudenthalTetSqEdges]

/-! ## §3. The headline: fiber value = literal table on EVERY bucket -/

/-- **GATE C-A2f HEADLINE (THEOREM): on EVERY bucket (every slot pair,
every integer phase key), the actual radical-bearing raw stencil
coefficient `J_{fg} / (2 * sqrt a*_f)` equals the real cast of the
independent literal rational table.**  The left side is
`rawJacobianCoefficient` of the interface audit (built from the
kernel-proved flat angle Jacobian and the flat tuple); the right side is
the bare literal table of §1.  The two sides are independently defined;
their equality is 36 kernel-checked radical cancellations. -/
theorem aggregate_raw_weight_eq_rational (b : Bucket) :
    rawJacobianCoefficient b.left b.right =
      ((rationalStencilWeight b : ℚ) : ℝ) := by
  have h := rawJacobianCoefficient_eval b.left b.right
  have htbl : rationalStencilWeight ⟨b.left, b.right, fun _ => 0⟩ =
      rationalStencilWeight b := rfl
  rw [htbl] at h
  exact h

/-- The literal table is invariant under the bucket reversal
`(f, g, u) ~ (g, f, -u)`: the underlying 6x6 rational matrix is symmetric,
so the intended external quotient is well-defined on table values. -/
theorem rationalStencilWeight_swap (b : Bucket) :
    rationalStencilWeight b.swap = rationalStencilWeight b := by
  rcases b with ⟨l, r, u⟩
  fin_cases l <;> fin_cases r <;> rfl

/-! ## §4. Consistency corollaries against the kernel-recorded audit facts -/

/-- The table reproduces the interface audit's row-0 smoke value
(`rawJacobianCoefficient (0,5) = 1/4`, kernel-recorded there). -/
theorem table_matches_row0Smoke :
    ((rationalStencilWeight row0SmokeBucket : ℚ) : ℝ) =
      rawJacobianCoefficient ⟨0, by decide⟩ ⟨5, by decide⟩ :=
  (aggregate_raw_weight_eq_rational row0SmokeBucket).symm

/-- The table reproduces the interface audit's worst-radical value
(`rawJacobianCoefficient (1,2) = -1/8`, kernel-recorded there through the
`-sqrt 2 / 4` Jacobian entry). -/
theorem table_matches_worstRadical :
    ((rationalStencilWeight worstRadicalBucket : ℚ) : ℝ) = -(1 / 8 : ℝ) := by
  rw [← aggregate_raw_weight_eq_rational worstRadicalBucket]
  exact ReggeTTBlochInterfaceAudit.worstRadical_rawJacobianCoefficient_closedForm

end

end ReggeTTBucketAggregation
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBucketAggregation.rawJacobianCoefficient_eq_norm_div
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBucketAggregation.rawJacobianCoefficient_eval
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBucketAggregation.aggregate_raw_weight_eq_rational
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBucketAggregation.rationalStencilWeight_swap
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBucketAggregation.table_matches_row0Smoke
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTBucketAggregation.table_matches_worstRadical

import IndisputableMonolith.Gravity.Analysis.ReggeTTFlatSecondVariation

/-!
# Regge TT Bloch interface audit, attempt 2

This is the panel-locked C11 interface audit surface.  Attempt 1 was rejected
because it wired the raw stencil and rational bucket table definitionally to
the objects they were supposed to audit.  This file therefore keeps the first
gate deliberately narrow and non-tautological:

* `rawCellStencil` is a literal `6 x 6 x 6`-shape triple sum over tetrahedra
  and ordered slot pairs.  The inner `g` sum of `flatSlotAngleDeriv` is
  expanded here, and `flatSlotSqrtDeriv` is written as
  `planeWaveTetVelocity / (2 * sqrt a*)`.
* `a2_reduced_eq_rawCellStencil` proves the A2 reduced value equals that
  triple sum by distributing the finite inner sum.  The sign follows the live
  A2 theorem: the reduced second variation is the negative Schlaefli-reduced
  contraction.
* The full rational bucket aggregation and assembled zero-mode cancellation
  are not claimed here.  The same-day sympy diagnostic found that the
  stencil-only constant block does not vanish; the ContinuumLimit engine must
  use the cosine two-jet route after the hinge/diagonal constant block is
  formally connected.

Status block:

* Gate A2-full (`aggregate_raw_weight_eq_rational` over all buckets): OPEN.
* Gate A3 (hinge-aware zero-mode): OPEN.
* Gate B (spike convention bridge): OPEN; the sidecar states
  `GateBConventionTarget`.

No ContinuumLimit or spike certificate module is imported here.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTBlochInterfaceAudit

open Geometry.PeriodicFreudenthalTorus
open Geometry.FreudenthalCubeTriangulation (freudenthalTetSqEdges)
open ReggeTTSymbolPreflight
open ReggeTTFlatSecondVariation

noncomputable section

/-- One raw term of the cell stencil: tetrahedron type and ordered slot pair.
The concrete finite sum below has `6 x 6 x 6 = 216` summands per periodic cell
type. -/
structure RawCellStencilTerm where
  tet : Fin 6
  left : Fin 6
  right : Fin 6
deriving DecidableEq, Repr

/-- Integer displacement key for phase buckets. -/
abbrev PhaseVector := Fin 3 → Int

/-- Bucket representative.  The intended external convention only identifies
`(f,g,u)` with `(g,f,-u)`; this attempt does not yet quotient or aggregate all
fibers. -/
structure Bucket where
  left : Fin 6
  right : Fin 6
  phase : PhaseVector
deriving DecidableEq, Repr

/-- Negate a phase key. -/
def negPhase (u : PhaseVector) : PhaseVector := fun i => -u i

/-- The reversal representative associated to `(f,g,u) ~ (g,f,-u)`. -/
def Bucket.swap (b : Bucket) : Bucket :=
  ⟨b.right, b.left, negPhase b.phase⟩

/-- Literal rational table placeholder for the bucket quarantine.  It is an
independent table, not a fiber sum.  Only the row-0 smoke bucket is proved
against actual Jacobian data in this attempt. -/
def rationalStencilWeight (b : Bucket) : ℚ :=
  match b.left, b.right with
  | ⟨0, _⟩, ⟨5, _⟩ => 1 / 4
  | ⟨5, _⟩, ⟨0, _⟩ => 1 / 4
  | _, _ => 0

/-- The reduced A2 canonical finite value, named for the interface audit. -/
def canonicalFiniteH (N : ℕ) [NeZero N] (E : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → ℤ) : ℝ :=
  (2 / (N : ℝ) ^ (3 : ℕ)) *
    (-∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
      flatSlotSqrtDeriv N E (commensurateMomentum N m) τ f *
        flatSlotAngleDeriv N E (commensurateMomentum N m) τ f)

/-- The raw triple stencil term, with the `g`-sum exposed and the sqrt-edge
factor unfolded to `v_f / (2 * sqrt a*_f)`. -/
def rawCellStencilTerm (N : ℕ) [NeZero N] (E : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → ℤ) (τ : PeriodicTet N N N) (f g : Fin 6) : ℝ :=
  (ReggeTTLocalSymbolExistence.planeWaveTetVelocity
      N E (commensurateMomentum N m) τ f /
      (2 * Real.sqrt (freudenthalTetSqEdges f))) *
    ReggeTTLocalSymbolExistence.planeWaveTetVelocity
      N E (commensurateMomentum N m) τ g *
      ReggeTTDerivativeGate.flatAngleJacobian f g

/-- Raw cell-stencil expression as an explicit triple sum. -/
def rawCellStencil (N : ℕ) [NeZero N] (E : Fin 3 → Fin 3 → ℝ)
    (m : Fin 3 → ℤ) : ℝ :=
  (2 / (N : ℝ) ^ (3 : ℕ)) *
    (-∑ τ : PeriodicTet N N N, ∑ f : Fin 6, ∑ g : Fin 6,
      rawCellStencilTerm N E m τ f g)

/-- Gate A1, honest part: the A2 reduced finite value equals the literal
triple raw stencil.  The proof is finite distribution of the inner
`flatSlotAngleDeriv` sum, not a definitional alias between the two sides.
The panel's `hN` premise is not needed: the incidence identity holds for
every `N` with `[NeZero N]`, which is a strictly stronger statement. -/
theorem a2_reduced_eq_rawCellStencil (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ) :
    canonicalFiniteH N E m = rawCellStencil N E m := by
  unfold canonicalFiniteH rawCellStencil rawCellStencilTerm
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  refine Finset.sum_congr rfl fun f _ => ?_
  unfold flatSlotSqrtDeriv flatSlotAngleDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  ring_nf

/-- Row-0 smoke-test bucket: `J_05 / (2 * sqrt a*_0)` with
`freudenthalTetSqEdges 0 = 1`, so this is radical-trivial. -/
def row0SmokeBucket : Bucket :=
  ⟨⟨0, by decide⟩, ⟨5, by decide⟩, fun _ => 0⟩

/-- Actual single-entry radical coefficient used by the early bucket
falsifier.  This is not the full fiber aggregation. -/
def rawJacobianCoefficient (f g : Fin 6) : ℝ :=
  ReggeTTDerivativeGate.flatAngleJacobian f g /
    (2 * Real.sqrt (freudenthalTetSqEdges f))

/-- Row-0 smoke test: the radical-trivial coefficient
`J_05 / (2 * sqrt a*_0)` is the literal rational `1/4`. -/
theorem row0Smoke_raw_weight_eq_rational :
    rawJacobianCoefficient ⟨0, by decide⟩ ⟨5, by decide⟩ = (1 / 4 : ℝ) := by
  unfold rawJacobianCoefficient
  change ReggeTTDerivativeGate.flatAngleJacobian (0 : Fin 6) ⟨5, by decide⟩ /
      (2 * Real.sqrt (freudenthalTetSqEdges (0 : Fin 6))) = (1 / 4 : ℝ)
  rw [ReggeTTDerivativeGate.flatAngleJacobian_row0_eval ⟨5, by decide⟩]
  norm_num [ReggeTTDerivativeGate.flatAngleJacobianRow0,
    freudenthalTetSqEdges, Real.sqrt_one]

/-- The independent table agrees with the row-0 smoke rational after casting
to real.  This is intentionally only the isolated smoke-test bucket, not the
full `aggregate_raw_weight_eq_rational` gate. -/
theorem row0Smoke_table_value :
    ((rationalStencilWeight row0SmokeBucket : ℚ) : ℝ) = (1 / 4 : ℝ) := by
  norm_num [rationalStencilWeight, row0SmokeBucket]

/-- Genuine radical-row bucket selected by the exact sympy generator:
`(f,g) = (1,2)`, where `freudenthalTetSqEdges 1 = 2` and the angle-Jacobian
entry is nonzero. -/
def worstRadicalBucket : Bucket :=
  ⟨⟨1, by decide⟩, ⟨2, by decide⟩, fun _ => 0⟩

/-- Genuine radical-row audit: at the row-Jacobian layer, individual raw
coefficients ARE irrational here; the panel's rationality claim lives at
bucket-fiber-AGGREGATION level and remains OPEN.  For this selected entry the
Jacobian is `-sqrt 2 / 4`; the current `rawJacobianCoefficient` normalization
then exposes and cancels the same `sqrt 2` denominator. -/
theorem worstRadical_flatAngleJacobian_value :
    ReggeTTDerivativeGate.flatAngleJacobian (1 : Fin 6) (2 : Fin 6) =
      -(Real.sqrt 2) / 4 := by
  rw [ReggeTTDerivativeGate.flatAngleJacobian_cofactor_form]
  rw [Geometry.CofactorDerivatives.dihedralCos3SqClosedFormDeriv_eq_poly]
  norm_num [ReggeTTDerivativeGate.flatArccosFactor,
    Geometry.CofactorDerivatives.dihedralCos3SqPolyClosedFormDeriv,
    Geometry.CofactorDerivatives.dihedralDenom3PolyClosedDerivValue,
    Geometry.CofactorDerivatives.dihedralDenom3Poly,
    Geometry.CofactorPolynomial.cmCofactor3Poly,
    Geometry.CofactorPolynomial.cmCofactorPartial,
    Geometry.DihedralCayleyMenger.oppositeCMVertices,
    freudenthalTetSqEdges]
  rw [show Real.sqrt 32 = 4 * Real.sqrt 2 by
    rw [show (32 : ℝ) = 16 * 2 by norm_num]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
      show Real.sqrt (16 : ℝ) = 4 by norm_num]]
  ring

/-- Exact raw coefficient for the genuine radical-row entry.  The statement
keeps the radical-bearing numerator visible; Lean also proves the normalized
coefficient simplifies to `-1/8`. -/
theorem worstRadical_rawJacobianCoefficient_closedForm :
    rawJacobianCoefficient ⟨1, by decide⟩ ⟨2, by decide⟩ = -(1 / 8 : ℝ) := by
  unfold rawJacobianCoefficient
  change ReggeTTDerivativeGate.flatAngleJacobian (1 : Fin 6) (2 : Fin 6) /
      (2 * Real.sqrt (freudenthalTetSqEdges (1 : Fin 6))) = -(1 / 8 : ℝ)
  rw [worstRadical_flatAngleJacobian_value]
  norm_num [freudenthalTetSqEdges]
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hsqrt2_ne]
  norm_num

/-- Generic Bloch fold over a supplied support and phase evaluator. -/
def reggeTTBlochFold (support : Finset Bucket) (phase : Bucket → ℝ)
    (amplitude : Bucket → ℝ) : ℝ :=
  support.sum fun b => phase b * amplitude b

/-- Cosine-evaluated assembled symbol surface. -/
def reggeTTAssembledSymbol (support : Finset Bucket) (phase : Bucket → ℝ)
    (amplitude : Bucket → ℝ) : ℝ :=
  reggeTTBlochFold support phase amplitude

/-- Moment evaluator surface.  The evaluator is the stencil fold at the
cosine two-jet value `-z^2/2`; the campaign's frozen `x(1/4)` normalization
is represented by the caller-supplied phase quadratic.  This file does not
identify that fold with the committed spike polynomial. -/
def reggeTTMoment (support : Finset Bucket) (phaseQuadratic : Bucket → ℝ)
    (amplitude : Bucket → ℝ) : ℝ :=
  reggeTTBlochFold support (fun b => -(phaseQuadratic b) / 2) amplitude

/-- Concrete record of the diagnostic zero-mode obstruction.  The
stencil-only constant block has the displayed nonzero residual for the
reported TT witness; the hinge/diagonal O(1) term is the remaining formal
interface piece needed before a true zero-mode theorem can be stated. -/
def stencilOnlyConstantWitnessResidual : ℝ :=
  -Real.pi * (Real.sqrt 2 + 4) / 8

end

end ReggeTTBlochInterfaceAudit
end Analysis
end Gravity
end IndisputableMonolith

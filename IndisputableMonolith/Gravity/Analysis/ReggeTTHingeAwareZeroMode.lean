import IndisputableMonolith.Gravity.Analysis.ReggeTTBucketAggregation

/-!
# Regge TT hinge-aware zero mode (Gate C-A3)

QG full-theory campaign, Paper C / Pillar 1, Lane C of the finishing
charter.  This module closes the hinge-aware zero-mode gate.

## What the sympy diagnostic found (context, not proof)

The same-day diagnostic (`state/qg_full_theory/bloch_sympy_diag/`) found
that the STENCIL-ONLY constant block (the full per-tet Hessian `G`
contracted with the edge-class coefficients, no hinge term) does NOT
vanish under TT; its residual at the reported TT witness
(`E = diag(1, -1, 0)/sqrt 2`, `k = e_z`) is `-pi*(sqrt 2 + 4)/8`,
kernel-recorded as
`ReggeTTBlochInterfaceAudit.stencilOnlyConstantWitnessResidual`.  The
diagnostic also found that the ASSEMBLED zero mode cancels: the report
records, verbatim, `hinge = pi*(-4 - sqrt(2))/8` (the SAME value as the
`Sigma_Gcc` residual) and `Hhat(0) quadratic = 0`.  The two recorded
values being EQUAL while the assembled quadratic vanishes fixes the
assembly sign convention: the assembled block combines them with a
relative minus sign, `assembled = hinge - Sigma_Gcc`.  The witness-tie
theorem below (`assembled_witness_split`) pins exactly this convention
in the kernel, so no silent sign change is possible.

## What THIS module proves (all THEOREM, about the ASSEMBLED block)

1. `hingeEdgeDiagonalBlock` is the assembled hinge/edge-diagonal O(1)
   block: `sum_d 2*pi * (-1/(4 * l2_d * sqrt l2_d)) * c_d(E)^2` over the
   seven displacement classes, with `c_d = polEdgeCoeff E d` the actual
   edge-class coefficients of the symbol program.
2. `hinge_cancels_recorded_residual`: at the reported TT witness the
   hinge block equals the kernel-recorded stencil-only residual
   `stencilOnlyConstantWitnessResidual` (the report records the same
   value for both, `-pi*(sqrt 2 + 4)/8`).  `assembled_witness_split`
   then ties all three objects in the kernel:
   `assembled(E_w) = hinge(E_w) - stencilOnlyConstantWitnessResidual`,
   with both sides zero, pinning the relative-minus assembly convention.
   (`ttWitness_isTT` checks the witness really is TT for `k = e_z`.)
3. `assembledConstantBlock_eq_zero`, THE ZERO-MODE HEADLINE: the
   Schlaefli-reduced assembled constant block (the `k = 0` value of the
   raw cell stencil, which by the proved Gate A2 reduction already
   carries the hinge and Hessian blocks combined) vanishes IDENTICALLY,
   for every polarization matrix.  Structure of the proof: the raw-table
   contraction over the six tetrahedron types is the PERFECT SQUARE
   `(c0 + c1 + c2 - c3 - c4 - c5 + c6)^2 / 2`
   (`zeroMode_free_coefficients`, an identity in seven free
   coefficients), and the alternating class sum vanishes for every
   polarization (`polEdgeCoeff_alternatingSum`, since
   `c_{x+y} + c_{x+z} + c_{y+z} = trace-double-count = c_x + c_y + c_z +
   c_{x+y+z}` termwise).
4. `canonicalFiniteH_zeroMomentum_eq_zero` and
   `zeroMomentum_symbol_is_zero`: the A2 canonical finite value at zero
   integer wave vector is `0` for every `N`, and the fixed-`N` TT Bloch
   symbol AT ZERO WAVE VECTOR exists and equals `0`: the lattice flat
   zero mode, as a statement about the true nonlinear Regge action's
   second variation.

## Why the headline carries NO TT hypotheses (binding disclosure)

The panel statement shape asked for the assembled constant block to
vanish "under the real TT hypotheses".  The kernel proof gives the
STRICTLY STRONGER statement: the assembled block vanishes for EVERY
polarization matrix, TT or not (constant metric perturbations are exact
flat directions of the lattice).  Stating the theorem with seven TT
hypotheses would make every one of them an UNUSED Prop hypothesis, which
this campaign's vacuity protocol forbids.  The TT instance is a special
case, and the witness-level theorem (2) exhibits the hinge-vs-stencil
cancellation on the concrete TT witness the diagnostic reported.

## What is NOT proved here (honest scope)

The full-Hessian decomposition `assembled = hinge - sum G c c` with `G`
the per-tet flat Regge Hessian is NOT re-proved in Lean (the theta
second-derivative entries of `G` are not formalized; the proved Gate A2
Schlaefli reduction makes them unnecessary for the assembled object).
The hinge-vs-full-`G` split is kernel-checked here only at the recorded
witness through (2); everywhere else it lives at sympy-diagnostic tier.

## Inherited axiom footprint (disclosure)

All theorems except the final corollary are pure algebra: expected
standard trio `[propext, Classical.choice, Quot.sound]`.
`zeroMomentum_symbol_is_zero` goes through the Gate A1/A2 chain
(`planeWave_TTBlochSymbolIs_reduced`), whose flat-point step rides the
certified periodic angle-sum chain: it therefore ALSO inherits
`Lean.ofReduceBool` and `Lean.trustCompiler` (inherited disclosure, not
new axioms).  `#print axioms` receipts at the end of the file.

No `sorry`, no `admit`, no new axioms, no `native_decide`, no `: True`
or `Nonempty`-only headline, no unused Prop hypotheses in this file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeTTHingeAwareZeroMode

open Geometry.PeriodicFreudenthalTorus
open Geometry.FreudenthalCubeTriangulation (freudenthalTetSqEdges)
open ReggeTTSymbolPreflight
open ReggeTTBlochInterfaceAudit
open ReggeTTBucketAggregation

noncomputable section

/-! ## §1. The hinge/edge-diagonal O(1) block -/

/-- THE ASSEMBLED HINGE/EDGE-DIAGONAL O(1) BLOCK: the `2*pi*L''` diagonal
of the real-space Regge Hessian at flat, contracted with the edge-class
coefficients of a polarization matrix.  `L(l2) = sqrt l2` gives
`L''(l2) = -1/(4 * l2 * sqrt l2)` at the flat squared length `l2_d` of
displacement class `d`; the factor `2*pi` is the deficit constant left on
the hinge diagonal because flat deficits vanish.  This mirrors, term for
term, the `hinge` object of the sympy diagnostic. -/
def hingeEdgeDiagonalBlock (E : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∑ d : Fin 7,
    2 * Real.pi *
      (-(1 / (4 * periodicDispSqEdge d * Real.sqrt (periodicDispSqEdge d)))) *
      (polEdgeCoeff E d) ^ 2

/-- The reported TT witness polarization of the diagnostic:
`E = diag(1, -1, 0) / sqrt 2`. -/
def ttWitnessPolarization : Fin 3 → Fin 3 → ℝ
  | 0, 0 => 1 / Real.sqrt 2 | 0, 1 => 0 | 0, 2 => 0
  | 1, 0 => 0 | 1, 1 => -(1 / Real.sqrt 2) | 1, 2 => 0
  | 2, 0 => 0 | 2, 1 => 0 | 2, 2 => 0

/-- The witness wave vector `k = e_z` (integer form `m = (0,0,1)`). -/
def ttWitnessWaveVector : Fin 3 → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1

private theorem sqrt2_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

private theorem inv_sqrt2_mul_self :
    (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
  rw [div_mul_div_comm, one_mul, sqrt2_mul_self]

private theorem inv_sqrt2_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [sq, inv_sqrt2_mul_self]

/-- The reported witness IS a TT polarization for `k = e_z`: symmetric,
traceless, transverse, Frobenius-normalized.  This grounds the phrase
"the reported TT witness" of the recorded residual. -/
theorem ttWitness_isTT :
    IsTTPolarization ttWitnessWaveVector ttWitnessPolarization := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp only [ttWitnessPolarization]
  · simp only [Fin.sum_univ_three, ttWitnessPolarization]
    ring
  · intro j
    fin_cases j <;>
      · simp only [Fin.sum_univ_three, ttWitnessPolarization,
          ttWitnessWaveVector]
        push_cast
        ring
  · simp only [Fin.sum_univ_three, ttWitnessPolarization]
    linear_combination 2 * inv_sqrt2_mul_self

/-- The seven edge-class coefficients of the witness, evaluated exactly:
`c = (1/sqrt 2, -1/sqrt 2, 0, 0, 1/sqrt 2, -1/sqrt 2, 0)`. -/
theorem ttWitness_polEdgeCoeff :
    polEdgeCoeff ttWitnessPolarization 0 = 1 / Real.sqrt 2 ∧
    polEdgeCoeff ttWitnessPolarization 1 = -(1 / Real.sqrt 2) ∧
    polEdgeCoeff ttWitnessPolarization 2 = 0 ∧
    polEdgeCoeff ttWitnessPolarization 3 = 0 ∧
    polEdgeCoeff ttWitnessPolarization 4 = 1 / Real.sqrt 2 ∧
    polEdgeCoeff ttWitnessPolarization 5 = -(1 / Real.sqrt 2) ∧
    polEdgeCoeff ttWitnessPolarization 6 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [polEdgeCoeff, Fin.sum_univ_three, ttWitnessPolarization,
        FreudenthalStencilPreflight.dispReal]
      ring

/-- **GATE C-A3, WITNESS-LEVEL CANCELLATION (THEOREM): at the reported TT
witness the assembled hinge/edge-diagonal block exactly equals the
kernel-recorded stencil-only residual.**  Since the assembled constant
block is `hinge - stencil`, this is the kernel statement that the
diagnostic's nonzero stencil-only obstruction is cancelled by the hinge
block at the witness:
`hinge(E_w) = -pi*(sqrt 2 + 4)/8 = stencilOnlyConstantWitnessResidual`. -/
theorem hinge_cancels_recorded_residual :
    hingeEdgeDiagonalBlock ttWitnessPolarization =
      stencilOnlyConstantWitnessResidual := by
  obtain ⟨h0, h1, h2c, h3, h4, h5, h6⟩ := ttWitness_polEdgeCoeff
  unfold hingeEdgeDiagonalBlock stencilOnlyConstantWitnessResidual
  rw [Fin.sum_univ_seven, h0, h1, h2c, h3, h4, h5, h6]
  simp only [periodicDispSqEdge, Real.sqrt_one, neg_sq]
  simp only [inv_sqrt2_sq]
  rw [show (1 : ℝ) / (4 * 2 * Real.sqrt 2) = Real.sqrt 2 / 16 by
    rw [div_eq_div_iff (by positivity) (by norm_num : (16 : ℝ) ≠ 0)]
    linear_combination (-8 : ℝ) * sqrt2_mul_self]
  ring

/-! ## §2. The slot displacement-class table, grounded -/

/-- Literal slot displacement-class table: `slotDispClass t f` is the
displacement class of local edge slot `f` of tetrahedron type `t`. -/
def slotDispClass : Fin 6 → Fin 6 → Fin 7
  | 0, 0 => 0 | 0, 1 => 3 | 0, 2 => 6 | 0, 3 => 1 | 0, 4 => 5 | 0, 5 => 2
  | 1, 0 => 0 | 1, 1 => 4 | 1, 2 => 6 | 1, 3 => 2 | 1, 4 => 5 | 1, 5 => 1
  | 2, 0 => 1 | 2, 1 => 3 | 2, 2 => 6 | 2, 3 => 0 | 2, 4 => 4 | 2, 5 => 2
  | 3, 0 => 1 | 3, 1 => 5 | 3, 2 => 6 | 3, 3 => 2 | 3, 4 => 4 | 3, 5 => 0
  | 4, 0 => 2 | 4, 1 => 4 | 4, 2 => 6 | 4, 3 => 0 | 4, 4 => 3 | 4, 5 => 1
  | 5, 0 => 2 | 5, 1 => 5 | 5, 2 => 6 | 5, 3 => 1 | 5, 4 => 3 | 5, 5 => 0

/-- GROUNDING (THEOREM): the literal table is exactly the displacement
class the ACTUAL periodic geometry assigns to slot `f` of tetrahedron
type `t`, in every cell of every torus (the class is cell-independent by
construction of `localEdgeOf`). -/
theorem slotDispClass_grounded (N : ℕ) [NeZero N] (cell : Vertex N N N)
    (t f : Fin 6) :
    (localEdgeOf cell t f).disp = slotDispClass t f := by
  fin_cases t <;> fin_cases f <;> rfl

/-! ## §3. The 36 raw coefficients as private rewrite lemmas

Each entry is `rawJacobianCoefficient_eval` (Gate C-A2f) evaluated on one
literal slot pair; keeping them separate keeps every `norm_num` call
small (the earlier single-shot expansion exceeded the local build memory
guard). -/

private theorem w00 : rawJacobianCoefficient 0 0 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 0 0]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w01 : rawJacobianCoefficient 0 1 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 0 1]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w02 : rawJacobianCoefficient 0 2 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 0 2]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w03 : rawJacobianCoefficient 0 3 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 0 3]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w04 : rawJacobianCoefficient 0 4 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 0 4]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w05 : rawJacobianCoefficient 0 5 = (1 / 4 : ℝ) := by
  rw [rawJacobianCoefficient_eval 0 5]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w10 : rawJacobianCoefficient 1 0 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 1 0]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w11 : rawJacobianCoefficient 1 1 = (1 / 8 : ℝ) := by
  rw [rawJacobianCoefficient_eval 1 1]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w12 : rawJacobianCoefficient 1 2 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 1 2]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w13 : rawJacobianCoefficient 1 3 = (-(1 / 4) : ℝ) := by
  rw [rawJacobianCoefficient_eval 1 3]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w14 : rawJacobianCoefficient 1 4 = (1 / 4 : ℝ) := by
  rw [rawJacobianCoefficient_eval 1 4]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w15 : rawJacobianCoefficient 1 5 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 1 5]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w20 : rawJacobianCoefficient 2 0 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 2 0]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w21 : rawJacobianCoefficient 2 1 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 2 1]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w22 : rawJacobianCoefficient 2 2 = (1 / 12 : ℝ) := by
  rw [rawJacobianCoefficient_eval 2 2]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w23 : rawJacobianCoefficient 2 3 = (1 / 4 : ℝ) := by
  rw [rawJacobianCoefficient_eval 2 3]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w24 : rawJacobianCoefficient 2 4 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 2 4]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w25 : rawJacobianCoefficient 2 5 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 2 5]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w30 : rawJacobianCoefficient 3 0 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 3 0]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w31 : rawJacobianCoefficient 3 1 = (-(1 / 4) : ℝ) := by
  rw [rawJacobianCoefficient_eval 3 1]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w32 : rawJacobianCoefficient 3 2 = (1 / 4 : ℝ) := by
  rw [rawJacobianCoefficient_eval 3 2]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w33 : rawJacobianCoefficient 3 3 = (1 / 4 : ℝ) := by
  rw [rawJacobianCoefficient_eval 3 3]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w34 : rawJacobianCoefficient 3 4 = (-(1 / 4) : ℝ) := by
  rw [rawJacobianCoefficient_eval 3 4]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w35 : rawJacobianCoefficient 3 5 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 3 5]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w40 : rawJacobianCoefficient 4 0 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 4 0]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w41 : rawJacobianCoefficient 4 1 = (1 / 4 : ℝ) := by
  rw [rawJacobianCoefficient_eval 4 1]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w42 : rawJacobianCoefficient 4 2 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 4 2]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w43 : rawJacobianCoefficient 4 3 = (-(1 / 4) : ℝ) := by
  rw [rawJacobianCoefficient_eval 4 3]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w44 : rawJacobianCoefficient 4 4 = (1 / 8 : ℝ) := by
  rw [rawJacobianCoefficient_eval 4 4]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w45 : rawJacobianCoefficient 4 5 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 4 5]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w50 : rawJacobianCoefficient 5 0 = (1 / 4 : ℝ) := by
  rw [rawJacobianCoefficient_eval 5 0]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w51 : rawJacobianCoefficient 5 1 = (-(1 / 8) : ℝ) := by
  rw [rawJacobianCoefficient_eval 5 1]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w52 : rawJacobianCoefficient 5 2 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 5 2]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w53 : rawJacobianCoefficient 5 3 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 5 3]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w54 : rawJacobianCoefficient 5 4 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 5 4]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]
private theorem w55 : rawJacobianCoefficient 5 5 = (0 : ℝ) := by
  rw [rawJacobianCoefficient_eval 5 5]; norm_num [ReggeTTBucketAggregation.rationalStencilWeight]

/-! ## §4. The assembled constant block and the zero-mode headline -/

/-- THE ASSEMBLED CONSTANT BLOCK, per periodic cell: the `k = 0` value of
the raw cell stencil of Gate A1/A2.  By the proved Schlaefli reduction
(Gate A2) this object ALREADY contains the hinge/edge-diagonal `2*pi*L''`
block and the per-tet Hessian block combined, with the relative sign of
the sympy report's convention (`assembled = hinge - Sigma_Gcc` at the
witness; see `assembled_witness_split`): the reduced second variation
`-sum_tau sum_f L'_f theta'_f` carries both blocks with no separate
theta-second-derivative term surviving.  `c_d = polEdgeCoeff E d` are
the same edge-class coefficients the hinge block uses. -/
def assembledConstantBlock (E : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6,
    rawJacobianCoefficient f g *
      polEdgeCoeff E (slotDispClass t f) *
      polEdgeCoeff E (slotDispClass t g)

/-- The raw-table contraction over the six tetrahedron types, in SEVEN
FREE coefficients, is the perfect square
`(c0 + c1 + c2 - c3 - c4 - c5 + c6)^2 / 2`.  This is the exact algebraic
shape of the assembled constant block: it does NOT vanish for free
coefficients (each per-tet block is individually nonzero and even the
six-type sum survives off the constraint surface); it vanishes exactly
on the alternating-sum hyperplane, where every geometric edge-class
coefficient vector lives. -/
theorem zeroMode_free_coefficients (c : Fin 7 → ℝ) :
    (∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6,
      rawJacobianCoefficient f g *
        c (slotDispClass t f) * c (slotDispClass t g)) =
      (c 0 + c 1 + c 2 - c 3 - c 4 - c 5 + c 6) ^ 2 / 2 := by
  simp only [Fin.sum_univ_six, slotDispClass]
  rw [w00, w01, w02, w03, w04, w05, w10, w11, w12, w13, w14, w15,
    w20, w21, w22, w23, w24, w25, w30, w31, w32, w33, w34, w35,
    w40, w41, w42, w43, w44, w45, w50, w51, w52, w53, w54, w55]
  ring

/-- The alternating class sum of the edge-class coefficients vanishes for
EVERY matrix `E`: the three face-diagonal classes double-count exactly
what the three axis classes and the body-diagonal class contribute
(`c_{x+y} + c_{x+z} + c_{y+z} = 2 tr + off = (c_x + c_y + c_z) +
c_{x+y+z}` at the level of the quadratic-form values). -/
theorem polEdgeCoeff_alternatingSum (E : Fin 3 → Fin 3 → ℝ) :
    polEdgeCoeff E 0 + polEdgeCoeff E 1 + polEdgeCoeff E 2 -
      polEdgeCoeff E 3 - polEdgeCoeff E 4 - polEdgeCoeff E 5 +
      polEdgeCoeff E 6 = 0 := by
  simp only [polEdgeCoeff, Fin.sum_univ_three,
    FreudenthalStencilPreflight.dispReal]
  ring

/-- **GATE C-A3 HEADLINE (THEOREM): the ASSEMBLED constant block vanishes
identically, for every polarization matrix.**  This is the hinge-aware
zero mode: the stencil-only block does NOT vanish (kernel-recorded
witness residual `-pi*(sqrt 2 + 4)/8`), but the assembled object, the
`k = 0` raw cell stencil, which by the Gate A2 Schlaefli reduction
carries the hinge and Hessian blocks combined, is exactly zero.  The
statement quantifies over ALL `E` (see the module docstring for why the
seven TT hypotheses would be unused and are therefore omitted); the TT
case demanded by the panel is the special case. -/
theorem assembledConstantBlock_eq_zero (E : Fin 3 → Fin 3 → ℝ) :
    assembledConstantBlock E = 0 := by
  unfold assembledConstantBlock
  have h := zeroMode_free_coefficients (fun d => polEdgeCoeff E d)
  simp only at h
  rw [h, polEdgeCoeff_alternatingSum]
  norm_num

/-- **WITNESS-LEVEL SPLIT (THEOREM): the assembled block, the hinge block,
and the recorded stencil-only residual are tied in the kernel at the
reported TT witness with the report's sign convention.**
`assembled(E_w) = hinge(E_w) - stencilOnlyConstantWitnessResidual`: the
sympy report records the SAME value `-pi*(sqrt 2 + 4)/8` for the hinge
block and the `Sigma_Gcc` residual, and the assembled quadratic vanishes,
so the assembly combines them with a relative minus sign.  This theorem
pins that convention: no silent sign change is possible, because all
three objects appear together in one kernel identity. -/
theorem assembled_witness_split :
    assembledConstantBlock ttWitnessPolarization =
      hingeEdgeDiagonalBlock ttWitnessPolarization -
        stencilOnlyConstantWitnessResidual := by
  rw [assembledConstantBlock_eq_zero, hinge_cancels_recorded_residual,
    sub_self]

/-! ## §5. Zero momentum kills the canonical finite value, every `N` -/

/-- Zero integer wave vector gives the zero commensurate momentum. -/
theorem commensurateMomentum_zero (N : ℕ) [NeZero N] :
    commensurateMomentum N (fun _ => (0 : ℤ)) = fun _ => (0 : ℝ) := by
  funext i
  simp [commensurateMomentum]

/-- At zero momentum every midpoint phase vanishes, so every plane-wave
velocity is the bare edge-class coefficient of its displacement class. -/
theorem planeWaveTetVelocity_zeroMomentum (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) (τ : PeriodicTet N N N) (f : Fin 6) :
    ReggeTTLocalSymbolExistence.planeWaveTetVelocity N E
        (fun _ => (0 : ℝ)) τ f =
      polEdgeCoeff E (slotDispClass τ.2 f) := by
  unfold ReggeTTLocalSymbolExistence.planeWaveTetVelocity
  rw [show edgeMidpointPhase N (fun _ => (0 : ℝ))
        (localEdgeOf τ.1 τ.2 f) = 0 by
    unfold edgeMidpointPhase
    simp]
  rw [Real.cos_zero, mul_one, slotDispClass_grounded N τ.1 τ.2 f]

/-- The `k = 0` raw cell stencil is `2` times the per-cell assembled
constant block: the cell sum contributes exactly `N ^ 3` identical
copies, and the `2 / N ^ 3` normalization leaves the factor `2`. -/
theorem rawCellStencil_zeroMomentum (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) :
    rawCellStencil N E (fun _ => (0 : ℤ)) = 2 * assembledConstantBlock E := by
  unfold rawCellStencil
  have hterm : ∀ (τ : PeriodicTet N N N) (f g : Fin 6),
      rawCellStencilTerm N E (fun _ => (0 : ℤ)) τ f g =
        rawJacobianCoefficient f g *
          polEdgeCoeff E (slotDispClass τ.2 f) *
          polEdgeCoeff E (slotDispClass τ.2 g) := by
    intro τ f g
    unfold rawCellStencilTerm rawJacobianCoefficient
    rw [commensurateMomentum_zero N,
      planeWaveTetVelocity_zeroMomentum N E τ f,
      planeWaveTetVelocity_zeroMomentum N E τ g]
    ring
  have hsum : (∑ τ : PeriodicTet N N N, ∑ f : Fin 6, ∑ g : Fin 6,
      rawCellStencilTerm N E (fun _ => (0 : ℤ)) τ f g) =
      (N : ℝ) ^ (3 : ℕ) *
        ∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6,
          rawJacobianCoefficient f g *
            polEdgeCoeff E (slotDispClass t f) *
            polEdgeCoeff E (slotDispClass t g) := by
    calc
      (∑ τ : PeriodicTet N N N, ∑ f : Fin 6, ∑ g : Fin 6,
          rawCellStencilTerm N E (fun _ => (0 : ℤ)) τ f g)
          = ∑ cell : Vertex N N N, ∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6,
              rawJacobianCoefficient f g *
                polEdgeCoeff E (slotDispClass t f) *
                polEdgeCoeff E (slotDispClass t g) := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl fun cell _ => ?_
            refine Finset.sum_congr rfl fun t _ => ?_
            refine Finset.sum_congr rfl fun f _ => ?_
            refine Finset.sum_congr rfl fun g _ => ?_
            exact hterm (cell, t) f g
      _ = (Fintype.card (Vertex N N N) : ℝ) *
            ∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6,
              rawJacobianCoefficient f g *
                polEdgeCoeff E (slotDispClass t f) *
                polEdgeCoeff E (slotDispClass t g) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = (N : ℝ) ^ (3 : ℕ) *
            ∑ t : Fin 6, ∑ f : Fin 6, ∑ g : Fin 6,
              rawJacobianCoefficient f g *
                polEdgeCoeff E (slotDispClass t f) *
                polEdgeCoeff E (slotDispClass t g) := by
            congr 1
            rw [show Fintype.card (Vertex N N N) = N * (N * N) by
              simp [Fintype.card_prod]]
            push_cast
            ring
  rw [hsum]
  unfold assembledConstantBlock
  have hN : ((N : ℝ)) ^ (3 : ℕ) ≠ 0 := by
    have hcast : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_neZero N).ne'
    positivity
  have hkey : ∀ (A S : ℝ), A ≠ 0 → (2 / A) * -(A * S) = 2 * -S := by
    intro A S hA
    field_simp
  exact hkey _ _ hN

/-- The A2 canonical finite value at zero integer wave vector vanishes
for every torus side `N` and every polarization matrix (pure algebra:
Gate A1 regrouping + the zero-mode headline). -/
theorem canonicalFiniteH_zeroMomentum_eq_zero (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) :
    canonicalFiniteH N E (fun _ => (0 : ℤ)) = 0 := by
  rw [a2_reduced_eq_rawCellStencil, rawCellStencil_zeroMomentum,
    assembledConstantBlock_eq_zero, mul_zero]

/-- **ZERO-MODE SYMBOL COROLLARY (THEOREM): the fixed-`N` TT Bloch symbol
of the TRUE nonlinear Regge action at ZERO wave vector exists and equals
`0`, for every `N` and every polarization matrix.**  This is the lattice
flat zero mode as a statement about the actual second variation, through
the Gate A1 existence chain and the Gate A2 reduction.  AXIOM
DISCLOSURE: this corollary (alone in this file) rides the certified
flat-deficit chain and therefore inherits `Lean.ofReduceBool` /
`Lean.trustCompiler` in addition to the standard trio. -/
theorem zeroMomentum_symbol_is_zero (N : ℕ) [NeZero N]
    (E : Fin 3 → Fin 3 → ℝ) :
    TTBlochSymbolIs N E (fun _ => (0 : ℤ)) 0 := by
  have h := ReggeTTFlatSecondVariation.planeWave_TTBlochSymbolIs_reduced
    N E (fun _ => (0 : ℤ))
  have hval : canonicalFiniteH N E (fun _ => (0 : ℤ)) =
      (2 / (N : ℝ) ^ (3 : ℕ)) *
        (-∑ τ : PeriodicTet N N N, ∑ f : Fin 6,
          ReggeTTFlatSecondVariation.flatSlotSqrtDeriv N E
              (commensurateMomentum N (fun _ => (0 : ℤ))) τ f *
            ReggeTTFlatSecondVariation.flatSlotAngleDeriv N E
              (commensurateMomentum N (fun _ => (0 : ℤ))) τ f) := rfl
  rw [← hval, canonicalFiniteH_zeroMomentum_eq_zero N E] at h
  exact h

end

end ReggeTTHingeAwareZeroMode
end Analysis
end Gravity
end IndisputableMonolith

#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.ttWitness_isTT
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.hinge_cancels_recorded_residual
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.slotDispClass_grounded
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.zeroMode_free_coefficients
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.polEdgeCoeff_alternatingSum
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.assembledConstantBlock_eq_zero
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.assembled_witness_split
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.canonicalFiniteH_zeroMomentum_eq_zero
#print axioms IndisputableMonolith.Gravity.Analysis.ReggeTTHingeAwareZeroMode.zeroMomentum_symbol_is_zero

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplex4D

/-!
# Complex-First 4D Wick Continuation of the Regge Hinge Data (C11 lane)

QG Seven-Gaps campaign, panel-locked flagship lane **C11** (panel P1-remainder,
judge verdict C11; referee **PROCEED-WITH-MANDATE**).  Hour-0 numeric gate
receipt: `state/qg_full_theory/wick_arc_trace/RESULTS.txt` (executed
2026-07-16; exact sympy crossing certificates + split-reading pass).

This module builds the complex-first formalization of the 4D Lorentzian Wick
continuation of the *hinge data* (complex Cayley-Menger areas-squared and
cofactor dihedral cosines) of the causal 4-simplex classes of
`Gravity.SevenGaps.CausalSimplex4D`, culminating in a boundary-continuation
theorem realized as a PATH-SELECTED continuation with a proved branch
certificate on the full open arc interior.

## Honest scope (mandated disclosure)

This is a **hinge-data continuation** (dihedral cosines and areas-squared of
triangular hinges of a single causal 4-simplex).  It may be called an
*action-level* continuation only if a genuine interior-hinge simplicial
complex exists; that is the separate C12 lane's question and is **not**
claimed here.  The FullTheoryLedger gap `wick_action_continuation_4d` /
`causalSimplex4DStatus.action_level_continuation_open` remains OPEN and no
ledger flag is touched by this module.

## The arc (S1)

The continuation path on the timelike squared edge is the canonical
upper-half-plane arc

  `z(t) = alpha * a^2 * exp(i * pi * (1 - t))`,  `t ∈ [0, 1]`,

with `z(0) = -(alpha * a^2)` the **Lorentzian** endpoint and
`z(1) = +(alpha * a^2)` the **Euclidean** endpoint, matching the repo sign
convention `lorentzianSqEdges` / `euclideanSqEdges`
(`CausalSimplex4D.lean:240-247`) and the executed gate (RESULTS.txt §1;
the endpoints are identified against the kernel-checked real tuples in
`continuationEdgesC_zero` / `continuationEdgesC_one` below).  The interior
`t ∈ (0,1)` lies strictly in the open upper half-plane.

## Split-sqrt denominator is MANDATORY (S2; gate verdict)

The complex cofactor dihedral cosine is defined with the denominator
**definitionally in split form** `csqrt C_pp * csqrt C_qq`, NOT
`csqrt (C_pp * C_qq)`.  The hour-0 gate proved the product form is KILLED by
interior branch crossings of the `Complex`-sqrt cut `(-∞, 0]`: exact
certificates (RESULTS.txt §3, alpha = 1, a = 1):

* fourOne timelike hinges and threeTwo (0,1,2): `C_pp*C_qq = 4*(3z-1)^2`
  crosses at `Re z = 1/3`, value exactly `-32`,
  `t* = 1 - arccos(1/3)/pi ≈ 0.6081734480`;
* threeTwo mixed hinges: `(8z-4)(6z-2)` crosses at `Re z = 5/12`, value
  exactly `-40`, `t* ≈ 0.6368017686`;
* threeTwo upper-pair hinges: `16*(2z-1)^2` crosses at `Re z = 1/2`, value
  exactly `-48`, `t* = 2/3` exactly;
* analogous exact crossings at alpha = 0.5 and alpha = 2 (not tuned).

These negative results are memorialized here as the kernel-checked theorem
`product_form_crossing` below (the fourOne offender: at
`tStar = 1 - arccos(1/3)/pi ∈ (0,1)` the cofactor product equals `-32`
exactly, a point ON the sqrt branch cut, off `Complex.slitPlane`).

## Mathlib cut conventions (verified against this toolchain)

Mathlib (this pin) has **no** `Complex.sqrt` and **no** `Complex.arccos`.
We therefore define `csqrt z := z ^ (1/2 : ℂ)` via `Complex.cpow`
(principal branch: `exp (log z / 2)`, `Complex.log` uses `arg ∈ (-π, π]`,
discontinuity exactly on `(-∞, 0]`; `Complex.continuousAt_cpow_const`
requires membership in `Complex.slitPlane = {z | 0 < re z ∨ im z ≠ 0}`,
which is exactly the complement of the cut).  The `BranchRegularOn`
predicate therefore encodes:

* sqrt-cut avoidance as membership in `Complex.slitPlane` (Mathlib's own
  slit-plane set, matching the cpow/log cut `(-∞, 0]`);
* arccos-cut avoidance directly as the region condition
  `im ≠ 0 ∨ (-1 < re ∧ re < 1)` (complement of the classical arccos cuts
  `(-∞, -1]` and `[1, ∞)` on the real axis, where any principal
  log-based `arccos` is continuous).

## What is proved (S3/S4 receipts)

For the traced fourOne timelike hinge — triangle `(0,1,4)`, opposite vertex
pair `(2,3)` (CM rows/cols 3 and 4), at `a = 1`, `alpha = 1` (the Lean
physical point `physicalCausalPent`):

* `branchRegular_fourOne_hinge` : `BranchRegularOn` holds on the FULL open
  arc interior `Set.Ioo 0 1` (not merely a subinterval).  Closed forms
  (kernel-checked 5x5 minors): `C_pp = C_qq = 6z - 2`, `C_pq = 1 - 2z`,
  hinge `areaSq = z/4 - 1/16`.  On the interior `im z > 0` forces every
  cofactor off the sqrt cut, and the split cosine has
  `im = -2 im z / normSq (6z-2) ≠ 0`, off the arccos cut (the trace's
  worst interior margin 0.4167 lives on threeTwo hinges; this fourOne
  hinge has margin 0.625, RESULTS.txt §3).
* `wick_boundary_continuation_fourOne_hinge` : the split-form cosine path
  is continuous on the CLOSED interval `[0,1]` (it equals the cut-free
  rational function `(1 - 2z)/(6z - 2)` wherever `6z - 2 ≠ 0`, proved for
  all `t ∈ ℝ` on this arc) and connects the Lorentzian endpoint value
  `-(3/8)` at `t = 0` to the Euclidean regular-4-simplex value `-(1/4)`
  at `t = 1` (`+C_pq` numerator convention of
  `Geometry.DihedralCayleyMenger`; textbook `-C` interior cosine `+1/4`).
* **Endpoint sign convention (S4, documented sign factor):** at the
  Lorentzian endpoint the cofactors are negative (`C_pp = C_qq = -8`, ON
  the sqrt cut boundary, `endpoint_cofactor_on_sqrt_cut`), and
  `csqrt w * csqrt w = w` (not `|w|`), so the split form equals
  `(-1) * (real product formula)`: split `-(3/8)` vs real-formula `+3/8`
  (`lorentzian_endpoint_sign_factor`).  NO unrestricted equality with the
  real Lorentzian formula is claimed.

## Honesty tiers (S5)

* MODEL: `SqEdges10C`, `pentDistSqC`, `cmMatrixC`, `cmMinorC`,
  `cmCofactorC`, `csqrt`, `dihedralDenomSplitC`, `dihedralCosSplitC`,
  `triCMMatrixC`, `triangleAreaSqC`, `hingeAreaSqC`, `arcZ`,
  `continuationEdgesC`, `OffArccosCut`, `BranchRegularOn` — definitional
  complexifications of the repo's real CM/dihedral conventions
  (`Geometry.CayleyMengerN`, `Geometry.DihedralCayleyMenger` 3D cofactor
  convention lifted to the 4D bordered 6x6 matrix).
* THEOREM: every declared theorem below is sorry-free and kernel-checked;
  in particular `branchRegular_fourOne_hinge` (inhabited certificate, full
  interior), `wick_boundary_continuation_fourOne_hinge`,
  `lorentzian_endpoint_sign_factor`, `product_form_crossing`.
* OPEN: the action-level continuation (interior-hinge complex, deficit
  angles, the continued Regge action itself) — C12 lane; nothing here
  closes it and no status flag is changed.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickActionComplexFirst

open CausalSimplex4D

/-! ## §1. Complex edge data and the bordered complex CM matrix (MODEL) -/

/-- Complex squared edge lengths of a 4-simplex, indexed by `Fin 10`
(lexicographic edge order of `CausalSimplex4D.pentEdgeVertices`). -/
abbrev SqEdges10C : Type := Fin 10 → ℂ

/-- Complex squared-distance table of the 4-simplex from the `Fin 10` edge
tuple (complexification of `CausalSimplex4D.pentDistSq`). -/
def pentDistSqC (x : SqEdges10C) : Fin 5 → Fin 5 → ℂ := fun i j =>
  match i.val, j.val with
  | 0, 1 => x 0
  | 1, 0 => x 0
  | 0, 2 => x 1
  | 2, 0 => x 1
  | 0, 3 => x 2
  | 3, 0 => x 2
  | 0, 4 => x 3
  | 4, 0 => x 3
  | 1, 2 => x 4
  | 2, 1 => x 4
  | 1, 3 => x 5
  | 3, 1 => x 5
  | 1, 4 => x 6
  | 4, 1 => x 6
  | 2, 3 => x 7
  | 3, 2 => x 7
  | 2, 4 => x 8
  | 4, 2 => x 8
  | 3, 4 => x 9
  | 4, 3 => x 9
  | _, _ => 0

/-- CM index to optional vertex: index `0` is the border row/column, index
`k+1` is vertex `k` (complexified mirror of
`Geometry.CayleyMengerN.cmIndexVertex` at `n = 4`). -/
def cmIndexVertexC (i : Fin 6) : Option (Fin 5) :=
  if h : i.val = 0 then none else some ⟨i.val - 1, by omega⟩

/-- The bordered `6 × 6` complex Cayley-Menger matrix of a complex edge
tuple (complexification of `Geometry.CayleyMengerN.cmMatrixN` at `n = 4`). -/
def cmMatrixC (x : SqEdges10C) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j =>
    match cmIndexVertexC i, cmIndexVertexC j with
    | none, none => 0
    | none, some _ => 1
    | some _, none => 1
    | some vi, some vj => pentDistSqC x vi vj

/-- Delete row `r` and column `c` from the complex CM matrix and take the
`5 × 5` determinant (mirror of `Geometry.CayleyMengerMatrix.cmMinor3`). -/
noncomputable def cmMinorC (x : SqEdges10C) (r c : Fin 6) : ℂ :=
  Matrix.det (Matrix.submatrix (cmMatrixC x) (Fin.succAbove r) (Fin.succAbove c))

/-- Cofactor sign `(-1)^(r+c)` as a complex number. -/
def cmCofactorSignC (r c : Fin 6) : ℂ :=
  if Even (r.val + c.val) then 1 else -1

/-- Complex Cayley-Menger cofactor `C_{r,c}` of the bordered `6 × 6` matrix
(mirror of `Geometry.CayleyMengerMatrix.cmCofactor3`). -/
noncomputable def cmCofactorC (x : SqEdges10C) (r c : Fin 6) : ℂ :=
  cmCofactorSignC r c * cmMinorC x r c

/-- Vertex index `0..4` to CM row/column index `1..5` (mirror of
`Geometry.DihedralCayleyMenger.cmVertexIndex`). -/
def cmVertexIndexC : Fin 5 → Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5

/-! ## §2. Principal-branch complex square root and the SPLIT cosine (MODEL) -/

/-- Principal-branch complex square root via `Complex.cpow`:
`csqrt z = z ^ (1/2 : ℂ) = exp (log z / 2)` for `z ≠ 0`, with branch cut on
`(-∞, 0]` (the complement of `Complex.slitPlane`).  Mathlib (this pin) has
no `Complex.sqrt`; this is the faithful principal-branch substitute. -/
noncomputable def csqrt (z : ℂ) : ℂ := z ^ (1 / 2 : ℂ)

/-- THEOREM: `csqrt z * csqrt z = z` for `z ≠ 0` (note: `= z`, NOT `= |z|`;
this is the source of the documented Lorentzian endpoint sign factor). -/
theorem csqrt_mul_self {z : ℂ} (hz : z ≠ 0) : csqrt z * csqrt z = z := by
  unfold csqrt
  rw [← Complex.cpow_add _ _ hz]
  have h : (1 / 2 + 1 / 2 : ℂ) = 1 := by norm_num
  rw [h, Complex.cpow_one]

/-- The SPLIT-form denominator of the complex cofactor dihedral cosine at
the hinge opposite the vertex pair `(p, q)`:
`csqrt C_pp * csqrt C_qq` — definitionally split, per the hour-0 gate
mandate (the single-sqrt product form `csqrt (C_pp * C_qq)` provably
crosses the sqrt cut mid-arc; see `product_form_crossing`). -/
noncomputable def dihedralDenomSplitC (x : SqEdges10C) (p q : Fin 5) : ℂ :=
  csqrt (cmCofactorC x (cmVertexIndexC p) (cmVertexIndexC p))
    * csqrt (cmCofactorC x (cmVertexIndexC q) (cmVertexIndexC q))

/-- The complex cofactor dihedral cosine (split form) at the hinge opposite
the vertex pair `(p, q)`; `+C_pq` numerator convention matching
`Geometry.DihedralCayleyMenger.dihedralCos3Sq` (which proves `+1/3` on the
regular unit tetrahedron in 3D; in 4D the same convention gives `-1/4` on
the regular unit 4-simplex, textbook `-C` interior cosine `+1/4`). -/
noncomputable def dihedralCosSplitC (x : SqEdges10C) (p q : Fin 5) : ℂ :=
  cmCofactorC x (cmVertexIndexC p) (cmVertexIndexC q) / dihedralDenomSplitC x p q

/-! ## §3. Complex triangle (hinge) area-squared (MODEL) -/

/-- The bordered `4 × 4` complex CM matrix of a triangle with squared edge
lengths `u = d(1,2)`, `v = d(1,3)`, `w = d(2,3)`. -/
def triCMMatrixC (u v w : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, _ => 1
    | _, 0 => 1
    | 1, 1 => 0
    | 2, 2 => 0
    | 3, 3 => 0
    | 1, 2 => u
    | 2, 1 => u
    | 1, 3 => v
    | 3, 1 => v
    | 2, 3 => w
    | 3, 2 => w
    | _, _ => 0

/-- Complex triangle area-squared, `-det(CM_4x4) / 16` (the `n = 2` case of
`Geometry.CayleyMengerN.simplexVolumeSqN`, complexified). -/
noncomputable def triangleAreaSqC (u v w : ℂ) : ℂ :=
  -(Matrix.det (triCMMatrixC u v w)) / 16

/-- Complex area-squared of the hinge triangle `{i, j, k}` of the 4-simplex
with complex edge tuple `x`. -/
noncomputable def hingeAreaSqC (x : SqEdges10C) (i j k : Fin 5) : ℂ :=
  triangleAreaSqC (pentDistSqC x i j) (pentDistSqC x i k) (pentDistSqC x j k)

/-! ## §4. The upper-half-plane Wick arc (S1, MODEL) -/

/-- The canonical upper-half-plane continuation arc on the timelike squared
edge: `arcZ a alpha t = alpha * a^2 * exp (i * pi * (1 - t))`.
Endpoints: `t = 0` Lorentzian (`-(alpha * a^2)`), `t = 1` Euclidean
(`+(alpha * a^2)`); interior strictly in `im > 0`.  Matches the executed
gate (RESULTS.txt §1) and the repo sign convention (see
`continuationEdgesC_zero` / `continuationEdgesC_one`). -/
noncomputable def arcZ (a alpha t : ℝ) : ℂ :=
  ((alpha * a ^ 2 : ℝ) : ℂ) * Complex.exp (((Real.pi * (1 - t) : ℝ) : ℂ) * Complex.I)

/-- The complex continuation of the causal squared-edge tuple along the
Wick arc: timelike edges follow `arcZ`, spacelike edges stay `a^2` (S1). -/
noncomputable def continuationEdgesC (ty : CausalPentType) (a alpha t : ℝ) :
    SqEdges10C :=
  fun e => if isTimelike ty e then arcZ a alpha t else ((a ^ 2 : ℝ) : ℂ)

/-- THEOREM: Lorentzian endpoint `t = 0` of the arc. -/
theorem arcZ_zero (a alpha : ℝ) : arcZ a alpha 0 = ((-(alpha * a ^ 2) : ℝ) : ℂ) := by
  unfold arcZ
  have h1 : (Real.pi * (1 - 0) : ℝ) = Real.pi := by ring
  rw [h1, Complex.exp_pi_mul_I]
  push_cast
  ring

/-- THEOREM: Euclidean endpoint `t = 1` of the arc. -/
theorem arcZ_one (a alpha : ℝ) : arcZ a alpha 1 = ((alpha * a ^ 2 : ℝ) : ℂ) := by
  unfold arcZ
  have h1 : (Real.pi * (1 - 1) : ℝ) = 0 := by ring
  rw [h1]
  simp

/-- THEOREM (endpoint identification): at `t = 0` the complex continuation
tuple is exactly the kernel-checked real Lorentzian tuple of
`CausalSimplex4D`, coerced to `ℂ`. -/
theorem continuationEdgesC_zero (ty : CausalPentType) (a alpha : ℝ) :
    continuationEdgesC ty a alpha 0
      = fun e => ((lorentzianSqEdges ty a alpha e : ℝ) : ℂ) := by
  funext e
  unfold continuationEdgesC lorentzianSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h, if_pos h, arcZ_zero]
  · rw [if_neg h, if_neg h]

/-- THEOREM (endpoint identification): at `t = 1` the complex continuation
tuple is exactly the kernel-checked real Euclideanized (Wick-rotated)
tuple of `CausalSimplex4D`, coerced to `ℂ`. -/
theorem continuationEdgesC_one (ty : CausalPentType) (a alpha : ℝ) :
    continuationEdgesC ty a alpha 1
      = fun e => ((euclideanSqEdges ty a alpha e : ℝ) : ℂ) := by
  funext e
  unfold continuationEdgesC euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h, if_pos h, arcZ_one]
  · rw [if_neg h, if_neg h]

/-! ## §5. The physical-point arc (`a = 1`, `alpha = 1`) -/

/-- The physical-point arc `zArc t = exp (i * pi * (1 - t))` (unit lattice
spacing, `alpha = 1`: the Lean physical point `physicalCausalPent`). -/
noncomputable def zArc (t : ℝ) : ℂ := arcZ 1 1 t

theorem zArc_eq_exp (t : ℝ) :
    zArc t = Complex.exp (((Real.pi * (1 - t) : ℝ) : ℂ) * Complex.I) := by
  unfold zArc arcZ
  norm_num

theorem zArc_re (t : ℝ) : (zArc t).re = Real.cos (Real.pi * (1 - t)) := by
  rw [zArc_eq_exp]
  exact Complex.exp_ofReal_mul_I_re _

theorem zArc_im (t : ℝ) : (zArc t).im = Real.sin (Real.pi * (1 - t)) := by
  rw [zArc_eq_exp]
  exact Complex.exp_ofReal_mul_I_im _

theorem zArc_zero : zArc 0 = -1 := by
  unfold zArc
  rw [arcZ_zero]
  norm_num

theorem zArc_one : zArc 1 = 1 := by
  unfold zArc
  rw [arcZ_one]
  norm_num

/-- THEOREM: the physical-point arc stays on the unit circle. -/
theorem normSq_zArc (t : ℝ) : Complex.normSq (zArc t) = 1 := by
  rw [Complex.normSq_apply, zArc_re, zArc_im]
  have h := Real.sin_sq_add_cos_sq (Real.pi * (1 - t))
  linear_combination h

/-- THEOREM: on the open arc interior the continued edge lies strictly in
the upper half-plane. -/
theorem zArc_im_pos {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : 0 < (zArc t).im := by
  rw [zArc_im]
  apply Real.sin_pos_of_pos_of_lt_pi
  · have h1 : 0 < 1 - t := by linarith [ht.2]
    exact mul_pos Real.pi_pos h1
  · have h1 : 1 - t < 1 := by linarith [ht.1]
    calc Real.pi * (1 - t) < Real.pi * 1 :=
          mul_lt_mul_of_pos_left h1 Real.pi_pos
    _ = Real.pi := mul_one _

theorem continuous_zArc : Continuous zArc := by
  have h : zArc = fun t : ℝ =>
      Complex.exp (((Real.pi * (1 - t) : ℝ) : ℂ) * Complex.I) :=
    funext zArc_eq_exp
  rw [h]
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_const.sub continuous_id))).mul
      continuous_const)

/-- THEOREM: the traced hinge's cofactor `6 z - 2` never vanishes anywhere
on the arc (including both endpoints): `|z| = 1` excludes `z = 1/3`. -/
theorem denom_ne (t : ℝ) : 6 * zArc t - 2 ≠ 0 := by
  intro h
  have h6 : (6 : ℂ) * zArc t = 2 := by linear_combination h
  have hns : Complex.normSq ((6 : ℂ) * zArc t) = Complex.normSq (2 : ℂ) := by
    rw [h6]
  rw [Complex.normSq_mul, normSq_zArc, mul_one, Complex.normSq_ofNat,
    Complex.normSq_ofNat] at hns
  norm_num at hns

/-! ## §6. Closed forms for the traced (4,1) timelike hinge

Hinge triangle `(0,1,4)`, opposite vertex pair `(2,3)` (CM rows/cols 3, 4),
type fourOne, `a = 1`: the RESULTS.txt named offender/certificate hinge.
The edge tuple has spacelike value `1` and timelike value `z`. -/

/-- The fourOne complex edge tuple at unit spacelike value and timelike
value `z` (this is `continuationEdgesC fourOne 1 1 t` at `z = zArc t`). -/
noncomputable def hingeEdgesC (z : ℂ) : SqEdges10C :=
  fun e => if isTimelike CausalPentType.fourOne e then z else 1

/-- THEOREM: the physical-point continuation tuple is the two-value tuple
at `z = zArc t`. -/
theorem continuationEdgesC_physical (t : ℝ) :
    continuationEdgesC CausalPentType.fourOne 1 1 t = hingeEdgesC (zArc t) := by
  funext e
  unfold continuationEdgesC hingeEdgesC zArc
  by_cases h : isTimelike CausalPentType.fourOne e = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    norm_num

/-- The explicit bordered `6 × 6` matrix of the fourOne tuple (spacelike 1,
timelike `z`): rows/cols 1..5 are vertices 0..4, apex vertex 4 is row/col
5 (mirror of `CausalSimplex4D.pentMatrix41` at `p = 1`, `q = z`). -/
def hingeMatrixC (z : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, _ => 1
    | _, 0 => 1
    | 1, 1 => 0
    | 2, 2 => 0
    | 3, 3 => 0
    | 4, 4 => 0
    | 5, 5 => 0
    | 1, 5 => z
    | 5, 1 => z
    | 2, 5 => z
    | 5, 2 => z
    | 3, 5 => z
    | 5, 3 => z
    | 4, 5 => z
    | 5, 4 => z
    | _, _ => 1

/-- THEOREM: the general complex CM matrix of the two-value tuple is the
explicit matrix. -/
theorem cmMatrixC_hingeEdges (z : ℂ) :
    cmMatrixC (hingeEdgesC z) = hingeMatrixC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The `5 × 5` minor of `hingeMatrixC` deleting row 3, column 3 (also,
by the vertex-2/vertex-3 symmetry, the (4,4) minor). -/
def minorPPC (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, _ => 1
    | _, 0 => 1
    | 1, 1 => 0
    | 2, 2 => 0
    | 3, 3 => 0
    | 4, 4 => 0
    | 1, 4 => z
    | 4, 1 => z
    | 2, 4 => z
    | 4, 2 => z
    | 3, 4 => z
    | 4, 3 => z
    | _, _ => 1

/-- The `5 × 5` minor of `hingeMatrixC` deleting row 3, column 4. -/
def minorPQC (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 0, _ => 1
    | _, 0 => 1
    | 1, 1 => 0
    | 2, 2 => 0
    | 4, 4 => 0
    | 1, 4 => z
    | 2, 4 => z
    | 3, 4 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | _, _ => 1

theorem submatrix_pp (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (3 : Fin 6))
      (Fin.succAbove (3 : Fin 6)) = minorPPC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem submatrix_qq (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (4 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minorPPC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem submatrix_pq (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (3 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minorPQC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
/-- THEOREM (symbolic 5x5 determinant): the diagonal minor is `6z - 2`
(RESULTS.txt closed form `C_pp = C_qq = 6z - 2`; at `z = 1` this is the
regular unit tetrahedron CM determinant 4). -/
theorem det_minorPPC (z : ℂ) : Matrix.det (minorPPC z) = 6 * z - 2 := by
  unfold minorPPC
  -- Style note: bare `simp` retained deliberately, mirroring the proved
  -- pattern of `CausalSimplex4D.det_pentMatrix41` (the default simp set's
  -- numeric simprocs are needed to keep the expansion tractable).
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
/-- THEOREM (symbolic 5x5 determinant): the off-diagonal minor is `2z - 1`
(cofactor sign `(-1)^7 = -1` gives `C_pq = 1 - 2z`). -/
theorem det_minorPQC (z : ℂ) : Matrix.det (minorPQC z) = 2 * z - 1 := by
  unfold minorPQC
  -- Style note: bare `simp` retained deliberately; see `det_minorPPC`.
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- THEOREM: closed form `C_pp = 6z - 2` (CM row/col 3, vertex 2). -/
theorem cofactor_pp (z : ℂ) :
    cmCofactorC (hingeEdgesC z) 3 3 = 6 * z - 2 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix_pp, det_minorPPC,
    if_pos (by decide : Even ((3 : Fin 6).val + (3 : Fin 6).val))]
  ring

/-- THEOREM: closed form `C_qq = 6z - 2` (CM row/col 4, vertex 3). -/
theorem cofactor_qq (z : ℂ) :
    cmCofactorC (hingeEdgesC z) 4 4 = 6 * z - 2 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix_qq, det_minorPPC,
    if_pos (by decide : Even ((4 : Fin 6).val + (4 : Fin 6).val))]
  ring

/-- THEOREM: closed form `C_pq = 1 - 2z` (CM rows/cols 3, 4). -/
theorem cofactor_pq (z : ℂ) :
    cmCofactorC (hingeEdgesC z) 3 4 = 1 - 2 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix_pq, det_minorPQC,
    if_neg (by decide : ¬ Even ((3 : Fin 6).val + (4 : Fin 6).val))]
  ring

set_option maxHeartbeats 2000000 in
/-- THEOREM: closed form of the hinge area-squared, `areaSq = z/4 - 1/16`
(hinge `(0,1,4)`: edges `(0,1) = 1` spacelike, `(0,4) = (1,4) = z`
timelike; at `z = 1` this is the regular hinge value `3/16`). -/
theorem hingeAreaSqC_closed (z : ℂ) :
    hingeAreaSqC (hingeEdgesC z) 0 1 4 = z / 4 - 1 / 16 := by
  unfold hingeAreaSqC triangleAreaSqC
  have h1 : pentDistSqC (hingeEdgesC z) 0 1 = 1 := rfl
  have h2 : pentDistSqC (hingeEdgesC z) 0 4 = z := rfl
  have h3 : pentDistSqC (hingeEdgesC z) 1 4 = z := rfl
  rw [h1, h2, h3]
  unfold triCMMatrixC
  -- Style note: bare `simp` retained deliberately; see `det_minorPPC`.
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-! ## §7. Branch regularity (S3) -/

/-- Off the classical arccos cuts `(-∞, -1]` and `[1, ∞)` on the real
axis: the open region where any principal (log-based) complex arccos is
continuous.  Mathlib has no `Complex.arccos`; the cut region is encoded
directly. -/
def OffArccosCut (w : ℂ) : Prop := w.im ≠ 0 ∨ (-1 < w.re ∧ w.re < 1)

/-- MODEL (S3 predicate): branch regularity of the split-form hinge
continuation on a parameter set `s`: both diagonal cofactors stay off the
`csqrt` branch cut (i.e. in `Complex.slitPlane`, the exact continuity
region of `Complex.cpow (1/2)`), and the split cosine ratio stays off the
arccos cuts. -/
def BranchRegularOn (x : ℝ → SqEdges10C) (p q : Fin 5) (s : Set ℝ) : Prop :=
  ∀ t ∈ s,
    cmCofactorC (x t) (cmVertexIndexC p) (cmVertexIndexC p) ∈ Complex.slitPlane
      ∧ cmCofactorC (x t) (cmVertexIndexC q) (cmVertexIndexC q) ∈ Complex.slitPlane
      ∧ OffArccosCut (dihedralCosSplitC (x t) p q)

/-- The split-form cosine path of the traced hinge along the physical
arc: `t ↦ C_pq / (csqrt C_pp * csqrt C_qq)` at hinge `(0,1,4)`, opposite
pair `(2,3)`, type fourOne, `a = alpha = 1`. -/
noncomputable def hingeCosPath (t : ℝ) : ℂ :=
  dihedralCosSplitC (continuationEdgesC CausalPentType.fourOne 1 1 t) 2 3

/-- THEOREM (branch collapse of the split form): everywhere on the arc the
split-form cosine equals the cut-free rational function
`(1 - 2z)/(6z - 2)` (the two split square roots multiply back to the
non-vanishing cofactor `6z - 2`).  This holds for ALL `t : ℝ`, endpoints
included. -/
theorem hingeCosPath_eq_moebius (t : ℝ) :
    hingeCosPath t = (1 - 2 * zArc t) / (6 * zArc t - 2) := by
  unfold hingeCosPath dihedralCosSplitC dihedralDenomSplitC
  rw [continuationEdgesC_physical]
  have hv2 : cmVertexIndexC 2 = 3 := rfl
  have hv3 : cmVertexIndexC 3 = 4 := rfl
  rw [hv2, hv3, cofactor_pp, cofactor_qq, cofactor_pq,
    csqrt_mul_self (denom_ne t)]

/-- THEOREM (S3 inhabitation certificate, FULL open interior): the traced
fourOne timelike hinge — triangle `(0,1,4)`, opposite pair `(2,3)`,
`a = 1`, `alpha = 1` — is branch-regular on ALL of `Set.Ioo 0 1`: both
cofactors `6z - 2` stay off the sqrt cut (their imaginary part `6 im z` is
strictly positive) and the split cosine stays off the arccos cuts (its
imaginary part `-2 im z / normSq (6z-2)` is strictly negative).  This is
the Lean transcription of the trace's interior margins (0.625 on this
hinge; RESULTS.txt §3). -/
theorem branchRegular_fourOne_hinge :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      2 3 (Set.Ioo 0 1) := by
  intro t ht
  dsimp only
  have hy : 0 < (zArc t).im := zArc_im_pos ht
  have hv2 : cmVertexIndexC 2 = 3 := rfl
  have hv3 : cmVertexIndexC 3 = 4 := rfl
  have him6 : (6 * zArc t - 2).im = 6 * (zArc t).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have hslit : 6 * zArc t - 2 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    rw [him6]
    exact (mul_pos (by norm_num : (0 : ℝ) < 6) hy).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [hv2, continuationEdgesC_physical, cofactor_pp]
    exact hslit
  · rw [hv3, continuationEdgesC_physical, cofactor_qq]
    exact hslit
  · left
    have hpath : dihedralCosSplitC (continuationEdgesC CausalPentType.fourOne 1 1 t) 2 3
        = hingeCosPath t := rfl
    rw [hpath, hingeCosPath_eq_moebius t]
    have hnum : (1 - 2 * zArc t).im * (6 * zArc t - 2).re
        - (1 - 2 * zArc t).re * (6 * zArc t - 2).im = -2 * (zArc t).im := by
      simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im, Complex.mul_re,
        Complex.one_im, Complex.one_re, Complex.re_ofNat, Complex.im_ofNat]
      ring
    have hdiv : ((1 - 2 * zArc t) / (6 * zArc t - 2)).im
        = (-2 * (zArc t).im) / Complex.normSq (6 * zArc t - 2) := by
      rw [Complex.div_im, div_sub_div_same, hnum]
    rw [hdiv]
    apply div_ne_zero
    · have hlt : (-2 : ℝ) * (zArc t).im < 0 :=
        mul_neg_of_neg_of_pos (by norm_num) hy
      exact ne_of_lt hlt
    · exact (Complex.normSq_pos.mpr (denom_ne t)).ne'

/-- THEOREM: the hinge area-squared also stays off the sqrt cut on the full
open interior (`im (z/4 - 1/16) = im z / 4 > 0`); at the Lorentzian
endpoint it sits ON the cut boundary (`-5/16`, the imaginary Lorentzian
area, an ALLOWED endpoint contact per the gate). -/
theorem hingeAreaSq_interior_off_cut {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    hingeAreaSqC (continuationEdgesC CausalPentType.fourOne 1 1 t) 0 1 4
      ∈ Complex.slitPlane := by
  rw [continuationEdgesC_physical, hingeAreaSqC_closed]
  apply Complex.mem_slitPlane_iff.mpr
  right
  have hy : 0 < (zArc t).im := zArc_im_pos ht
  have him : (zArc t / 4 - 1 / 16).im = (zArc t).im / 4 := by
    simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im]
    ring
  rw [him]
  exact (div_pos hy (by norm_num : (0 : ℝ) < 4)).ne'

/-! ## §8. The boundary-continuation theorem (S4) -/

/-- THEOREM: the split-form cosine path is continuous on the CLOSED
interval `[0, 1]` (it coincides there with the cut-free rational function
of the arc, whose denominator never vanishes). -/
theorem continuousOn_hingeCosPath : ContinuousOn hingeCosPath (Set.Icc 0 1) := by
  have hmo : Continuous fun t => (1 - 2 * zArc t) / (6 * zArc t - 2) := by
    apply Continuous.div
    · exact continuous_const.sub (continuous_const.mul continuous_zArc)
    · exact (continuous_const.mul continuous_zArc).sub continuous_const
    · exact fun t => denom_ne t
  exact hmo.continuousOn.congr fun t _ => hingeCosPath_eq_moebius t

/-- THEOREM: Lorentzian endpoint value of the SPLIT form: `-(3/8)`.
(The real product-form formula gives `+3/8` here; see
`lorentzian_endpoint_sign_factor` for the documented sign factor.) -/
theorem hingeCosPath_zero : hingeCosPath 0 = -(3 / 8 : ℂ) := by
  rw [hingeCosPath_eq_moebius, zArc_zero]
  norm_num

/-- THEOREM: Euclidean endpoint value: `-(1/4)`, the regular unit
4-simplex value in the `+C_pq` convention (textbook `-C` interior dihedral
cosine `+1/4`; RESULTS.txt endpoint table). -/
theorem hingeCosPath_one : hingeCosPath 1 = -(1 / 4 : ℂ) := by
  rw [hingeCosPath_eq_moebius, zArc_one]
  norm_num

/-- THEOREM (S4, the boundary-continuation receipt): the split-form
complex dihedral cosine of the traced fourOne timelike hinge is a
continuous path on `[0, 1]` connecting the Lorentzian endpoint value
`-(3/8)` at `t = 0` to the Euclidean regular-4-simplex value `-(1/4)` at
`t = 1`.  The Lorentzian endpoint carries the documented sign factor
relative to the real product-form formula (`lorentzian_endpoint_sign_factor`);
no unrestricted equality with the real Lorentzian formula is claimed. -/
theorem wick_boundary_continuation_fourOne_hinge :
    ContinuousOn hingeCosPath (Set.Icc 0 1)
      ∧ hingeCosPath 0 = -(3 / 8 : ℂ)
      ∧ hingeCosPath 1 = -(1 / 4 : ℂ) :=
  ⟨continuousOn_hingeCosPath, hingeCosPath_zero, hingeCosPath_one⟩

/-- The real product-form (single `Real.sqrt` of the cofactor product)
Lorentzian value at the endpoint `z = -1`:
`C_pq / Real.sqrt (C_pp * C_qq) = 3 / sqrt 64 = 3/8`. -/
noncomputable def realLorentzianProductCos : ℝ :=
  (1 - 2 * (-1 : ℝ)) / Real.sqrt ((6 * (-1 : ℝ) - 2) * (6 * (-1 : ℝ) - 2))

theorem realLorentzianProductCos_eq : realLorentzianProductCos = 3 / 8 := by
  unfold realLorentzianProductCos
  have h64 : ((6 * (-1 : ℝ) - 2) * (6 * (-1 : ℝ) - 2)) = 64 := by norm_num
  rw [h64, show (64 : ℝ) = 8 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num

/-- THEOREM (S4 documented sign convention): at the Lorentzian endpoint,
where both cofactors are negative (`C_pp = C_qq = -8`), the split form
equals `(-1) *` (the real product-form value): `csqrt w * csqrt w = w`,
not `|w|`, so the split denominator is `-8` where `Real.sqrt 64 = +8`.
The sign factor is exactly `-1` on this hinge (trace: split `-3/8` vs
real-formula `+3/8`, RESULTS.txt §3 endpoint note). -/
theorem lorentzian_endpoint_sign_factor :
    hingeCosPath 0 = (-1 : ℂ) * ((realLorentzianProductCos : ℝ) : ℂ) := by
  rw [hingeCosPath_zero, realLorentzianProductCos_eq]
  push_cast
  ring

/-- THEOREM (endpoint cut contact, honest disclosure): at the Lorentzian
endpoint the diagonal cofactor is `-8`, which lies ON the `csqrt` branch
cut (off `Complex.slitPlane`).  The branch certificate is therefore stated
on the OPEN interior; the endpoint values themselves are still exact
(`hingeCosPath_zero`) because the split form collapses to the cut-free
rational function (`hingeCosPath_eq_moebius`). -/
theorem endpoint_cofactor_on_sqrt_cut :
    cmCofactorC (continuationEdgesC CausalPentType.fourOne 1 1 0) 3 3 = -8
      ∧ (-8 : ℂ) ∉ Complex.slitPlane := by
  constructor
  · rw [continuationEdgesC_physical, cofactor_pp, zArc_zero]
    ring
  · intro hmem
    rw [Complex.mem_slitPlane_iff] at hmem
    simp at hmem
    linarith

/-! ## §9. The product-form negative certificate (gate FAIL, memorialized) -/

/-- The exact interior crossing parameter of the product form on this
hinge: `tStar = 1 - arccos(1/3)/pi ≈ 0.6081734480` (RESULTS.txt §3,
named canonical offender). -/
noncomputable def tStar : ℝ := 1 - Real.arccos (1 / 3) / Real.pi

theorem tStar_mem_Ioo : tStar ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi := Real.pi_pos
  have h1 : 0 < Real.arccos (1 / 3) := Real.arccos_pos.mpr (by norm_num)
  have h2 : Real.arccos (1 / 3) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (by norm_num)
  constructor
  · have hle : Real.arccos (1 / 3) / Real.pi ≤ 1 / 2 := by
      rw [div_le_iff₀ hpi]
      linarith
    unfold tStar
    linarith
  · have hgt : 0 < Real.arccos (1 / 3) / Real.pi := div_pos h1 hpi
    unfold tStar
    linarith

theorem arg_tStar : Real.pi * (1 - tStar) = Real.arccos (1 / 3) := by
  have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold tStar
  have h : (1 : ℝ) - (1 - Real.arccos (1 / 3) / Real.pi)
      = Real.arccos (1 / 3) / Real.pi := by ring
  rw [h, mul_comm, div_mul_cancel₀ _ hpne]

theorem cos_arg_tStar : Real.cos (Real.pi * (1 - tStar)) = 1 / 3 := by
  rw [arg_tStar]
  exact Real.cos_arccos (by norm_num) (by norm_num)

/-- THEOREM (exact crossing value): at `tStar` the arc point is
`z = 1/3 + i * sin(arccos(1/3))` and the product-form denominator argument
`C_pp * C_qq = (6z - 2)^2` equals `-32` EXACTLY: a real negative value in
the interior of the arc. -/
theorem product_form_crossing_value :
    (6 * zArc tStar - 2) * (6 * zArc tStar - 2) = -32 := by
  have hz : zArc tStar = ((1 / 3 : ℝ) : ℂ)
      + ((Real.sin (Real.pi * (1 - tStar)) : ℝ) : ℂ) * Complex.I := by
    rw [zArc_eq_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, cos_arg_tStar]
  have h6z : 6 * zArc tStar - 2
      = ((Real.sin (Real.pi * (1 - tStar)) : ℝ) : ℂ) * Complex.I * 6 := by
    rw [hz]
    push_cast
    ring
  have hprod : (6 * zArc tStar - 2) * (6 * zArc tStar - 2)
      = -(36 : ℂ) * ((Real.sin (Real.pi * (1 - tStar)) : ℝ) : ℂ) ^ 2 := by
    rw [h6z]
    linear_combination (36 * ((Real.sin (Real.pi * (1 - tStar)) : ℝ) : ℂ) ^ 2)
      * Complex.I_sq
  have hs2 : Real.sin (Real.pi * (1 - tStar)) ^ 2 = 8 / 9 := by
    rw [Real.sin_sq, cos_arg_tStar]
    norm_num
  have hcast : ((Real.sin (Real.pi * (1 - tStar)) : ℝ) : ℂ) ^ 2
      = ((8 / 9 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hs2]
  rw [hprod, hcast]
  push_cast
  norm_num

/-- THEOREM (the gate's FAIL event, kernel-checked): at the interior arc
parameter `tStar ∈ (0, 1)` the product `C_pp * C_qq` of the traced hinge's
diagonal cofactors equals `-32` exactly, which lies ON the `csqrt` branch
cut (off `Complex.slitPlane`).  This is the negative certificate that
KILLS the literal single-sqrt product transcription
`csqrt (C_pp * C_qq)` of the 3D formula
`Geometry.DihedralCayleyMenger.dihedralDenom3`, and it is why
`dihedralDenomSplitC` is definitionally split (RESULTS.txt final verdict:
product FAIL, split PASS). -/
theorem product_form_crossing :
    tStar ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.fourOne 1 1 tStar) 3 3
          * cmCofactorC (continuationEdgesC CausalPentType.fourOne 1 1 tStar) 4 4
          = -32
      ∧ (-32 : ℂ) ∉ Complex.slitPlane := by
  refine ⟨tStar_mem_Ioo, ?_, ?_⟩
  · rw [continuationEdgesC_physical, cofactor_pp, cofactor_qq]
    exact product_form_crossing_value
  · intro hmem
    rw [Complex.mem_slitPlane_iff] at hmem
    simp at hmem
    linarith

/-! ## §10. Axiom audit

`#print axioms` receipts for the load-bearing theorems.  Expected output
for each: `[propext, Classical.choice, Quot.sound]` (the standard Mathlib
trio; no `sorryAx`, no `Lean.ofReduceBool`, no repo-local axioms).  The
output appears as `info` lines in the build log. -/

#print axioms branchRegular_fourOne_hinge
#print axioms wick_boundary_continuation_fourOne_hinge
#print axioms lorentzian_endpoint_sign_factor
#print axioms product_form_crossing
#print axioms hingeAreaSq_interior_off_cut
#print axioms endpoint_cofactor_on_sqrt_cut

end WickActionComplexFirst
end SevenGaps
end Gravity
end IndisputableMonolith

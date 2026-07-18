import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import IndisputableMonolith.Gravity.SevenGaps.WickActionComplexFirst
import IndisputableMonolith.Gravity.SevenGaps.WickFourOneAllHinges

/-!
# All-Hinge Complex-First Wick Continuation of the (3,2) Causal 4-Simplex (Lane B2)

QG Seven-Gaps campaign, lane B of the finishing charter, second deliverable:
the split-form branch certificate and boundary continuation for ALL TEN
triangular hinges of the threeTwo causal 4-simplex, at the physical point
`a = 1`, `alpha = 1`, on the canonical upper-half-plane arc `zArc` of
`WickActionComplexFirst`, plus the TWO remaining product-form kill
certificates of the executed trace
(`state/qg_full_theory/wick_arc_trace/RESULTS.txt`).

## Hinge classes (opposite pair `{p, q}` determines the hinge)

For the threeTwo type (lower slice `{0,1,2}`, upper slice `{3,4}`; timelike
edges exactly the six cross edges, `CausalSimplex4D.isTimelike`):

* opposite pair `(3,4)` (1 pair): the SPACELIKE hinge `(0,1,2)`; closed
  forms `C_pp = C_qq = 6z - 2`, `C_pq = 5 - 6z`, `areaSq = 3/16`;
* mixed pairs, one lower one upper (6 pairs): hinges with 2 timelike
  triangle edges; ASYMMETRIC cofactors `C_pp = 8z - 4` (lower member),
  `C_qq = 6z - 2` (upper member), `C_pq = -1`, `areaSq = z/4 - 1/16`;
* pairs inside the lower triple (3 pairs): the UPPER-PAIR hinges
  `(0,3,4)`, `(1,3,4)`, `(2,3,4)`; closed forms `C_pp = C_qq = 8z - 4`,
  `C_pq = 3 - 4z`, `areaSq = z/4 - 1/16`.

All closed forms kernel-checked below by explicit 5x5 minors, matching the
trace's per-hinge table.

## Honest endpoint disclosure for the spacelike hinge (0,1,2)

At the Lorentzian endpoint `t = 0` the split cosine of the spacelike hinge
equals `-(11/8)`, which sits exactly ON the arccos cut (`im = 0`,
`|re| ≥ 1`): the classical Lorentzian boost angle at the spacelike hinge of
a (3,2) simplex.  This is an ALLOWED endpoint contact under the executed
gate; the branch certificate is therefore stated on the OPEN interior only,
where the cosine's imaginary part equals `-18 im z / normSq (6z - 2)`,
strictly negative.  The endpoint VALUE itself is still exact (the split
form collapses to the cut-free rational function `(5 - 6z)/(6z - 2)`).

## Product-form kill certificates (negative results, memorialized)

The single-sqrt product transcription `csqrt (C_pp * C_qq)` is KILLED on
the threeTwo type by two further interior branch crossings (the fourOne
crossing `-32` is memorialized in the landed module):

* mixed class: `(8z - 4)(6z - 2)` is exactly `-40` at
  `Re z = 5/12`, `t* = 1 - arccos(5/12)/pi ≈ 0.6368017686`
  (`product_form_crossing_threeTwo_mixed`);
* upper-pair class: `(8z - 4)^2 = 16 (2z - 1)^2` is exactly `-48` at
  `Re z = 1/2`, `t* = 2/3` EXACTLY
  (`product_form_crossing_threeTwo_upper`).

## Honesty tiers

* MODEL: `hingeEdges32C`, `hingeMatrix32C`, `threeTwoCosPath` and the
  explicit minor matrices are definitional (complexifications inherited
  from `WickActionComplexFirst`; no new modeling choices).
* THEOREM: every declared theorem below is sorry-free and kernel-checked.
* OPEN: the action-level continuation (interior-hinge simplicial complex,
  deficit angles, the continued Regge action) is NOT claimed (C12 lane).
  No `FullTheoryLedger` flag is touched.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickThreeTwoHinges

open CausalSimplex4D
open WickActionComplexFirst
open WickFourOneAllHinges

/-! ## §1. The threeTwo complex edge tuple and its bordered matrix (MODEL) -/

/-- The threeTwo complex edge tuple at unit spacelike value and timelike
value `z` (this is `continuationEdgesC threeTwo 1 1 t` at `z = zArc t`). -/
noncomputable def hingeEdges32C (z : ℂ) : SqEdges10C :=
  fun e => if isTimelike CausalPentType.threeTwo e then z else 1

/-- THEOREM: the physical-point threeTwo continuation tuple is the
two-value tuple at `z = zArc t`. -/
theorem continuationEdgesC_physical32 (t : ℝ) :
    continuationEdgesC CausalPentType.threeTwo 1 1 t
      = hingeEdges32C (zArc t) := by
  funext e
  unfold continuationEdgesC hingeEdges32C zArc
  by_cases h : isTimelike CausalPentType.threeTwo e = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    norm_num

/-- The explicit bordered `6 × 6` matrix of the threeTwo tuple (spacelike
1, timelike `z`): rows/cols 1..3 are the lower-slice vertices 0..2,
rows/cols 4..5 the upper-slice vertices 3..4 (mirror of
`CausalSimplex4D.pentMatrix32` at `p = 1`, `q = z`). -/
def hingeMatrix32C (z : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
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
    | 1, 2 => 1
    | 2, 1 => 1
    | 1, 3 => 1
    | 3, 1 => 1
    | 2, 3 => 1
    | 3, 2 => 1
    | 4, 5 => 1
    | 5, 4 => 1
    | _, _ => z

/-- THEOREM: the general complex CM matrix of the threeTwo two-value tuple
is the explicit matrix. -/
theorem cmMatrixC_hingeEdges32 (z : ℂ) :
    cmMatrixC (hingeEdges32C z) = hingeMatrix32C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## §2. Per-pair 5x5 minors (kernel-checked; sympy-cross-checked) -/

/-- Upper diagonal minor deleting CM row/col 4 (vertex 3): the remaining
four vertices form the `(1,1,1; z,z,z)` tetrahedron, i.e. the landed
`minorPPC` matrix. -/
theorem submatrix32_44 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (4 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minorPPC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Upper diagonal minor deleting CM row/col 5 (vertex 4): again the landed
`minorPPC`. -/
theorem submatrix32_55 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (5 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minorPPC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Lower diagonal minor (delete any lower vertex; the three deletions give
the SAME explicit matrix): the `2 + 2` tetrahedron with two spacelike and
four timelike edges. -/
def minor32LowerC (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 3 => z
    | 1, 4 => z
    | 2, 2 => 0
    | 2, 3 => z
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix32_11 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (1 : Fin 6)) = minor32LowerC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem submatrix32_22 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (2 : Fin 6)) = minor32LowerC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem submatrix32_33 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (3 : Fin 6))
      (Fin.succAbove (3 : Fin 6)) = minor32LowerC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
/-- THEOREM (symbolic 5x5 determinant): the lower diagonal minor is
`8z - 4` (trace closed form; at `z = 1` the regular value 4). -/
theorem det_minor32LowerC (z : ℂ) :
    Matrix.det (minor32LowerC z) = 8 * z - 4 := by
  unfold minor32LowerC
  -- Style note: bare `simp` retained deliberately, mirroring
  -- `WickActionComplexFirst.det_minorPPC`.
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Off-diagonal minor at CM (4,5) (opposite pair (3,4), spacelike
hinge). -/
def minor32_45C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 4 => z
    | 2, 2 => 0
    | 2, 4 => z
    | 3, 3 => 0
    | 3, 4 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | _, _ => 1

theorem submatrix32_45 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (4 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor32_45C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_45C (z : ℂ) : Matrix.det (minor32_45C z) = 6 * z - 5 := by
  unfold minor32_45C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Mixed off-diagonal minor at CM (1,4) (opposite pair (0,3)). -/
def minor32_14C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 2 => 0
    | 1, 4 => z
    | 2, 3 => 0
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix32_14 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minor32_14C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_14C (z : ℂ) : Matrix.det (minor32_14C z) = 1 := by
  unfold minor32_14C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Mixed off-diagonal minor at CM (1,5) (opposite pair (0,4)). -/
def minor32_15C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 2 => 0
    | 1, 4 => z
    | 2, 3 => 0
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => z
    | 3, 4 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | _, _ => 1

theorem submatrix32_15 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor32_15C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_15C (z : ℂ) : Matrix.det (minor32_15C z) = -1 := by
  unfold minor32_15C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Mixed off-diagonal minor at CM (2,4) (opposite pair (1,3)). -/
def minor32_24C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 4 => z
    | 2, 3 => 0
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix32_24 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minor32_24C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_24C (z : ℂ) : Matrix.det (minor32_24C z) = -1 := by
  unfold minor32_24C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Mixed off-diagonal minor at CM (2,5) (opposite pair (1,4)). -/
def minor32_25C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 4 => z
    | 2, 3 => 0
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => z
    | 3, 4 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | _, _ => 1

theorem submatrix32_25 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor32_25C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_25C (z : ℂ) : Matrix.det (minor32_25C z) = 1 := by
  unfold minor32_25C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Mixed off-diagonal minor at CM (3,4) (opposite pair (2,3)). -/
def minor32_34C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 4 => z
    | 2, 2 => 0
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix32_34 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (3 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minor32_34C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_34C (z : ℂ) : Matrix.det (minor32_34C z) = 1 := by
  unfold minor32_34C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Mixed off-diagonal minor at CM (3,5) (opposite pair (2,4)). -/
def minor32_35C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 4 => z
    | 2, 2 => 0
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => z
    | 3, 4 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | _, _ => 1

theorem submatrix32_35 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (3 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor32_35C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_35C (z : ℂ) : Matrix.det (minor32_35C z) = -1 := by
  unfold minor32_35C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Upper-pair off-diagonal minor at CM (1,2) (opposite pair (0,1)). -/
def minor32_12C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 3 => z
    | 1, 4 => z
    | 2, 2 => 0
    | 2, 3 => z
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix32_12 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (2 : Fin 6)) = minor32_12C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_12C (z : ℂ) : Matrix.det (minor32_12C z) = 4 * z - 3 := by
  unfold minor32_12C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Upper-pair off-diagonal minor at CM (1,3) (opposite pair (0,2)). -/
def minor32_13C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 2 => 0
    | 1, 3 => z
    | 1, 4 => z
    | 2, 3 => z
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix32_13 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (3 : Fin 6)) = minor32_13C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_13C (z : ℂ) : Matrix.det (minor32_13C z) = 3 - 4 * z := by
  unfold minor32_13C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Upper-pair off-diagonal minor at CM (2,3) (opposite pair (1,2)). -/
def minor32_23C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 3 => z
    | 1, 4 => z
    | 2, 3 => z
    | 2, 4 => z
    | 3, 1 => z
    | 3, 2 => z
    | 3, 3 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix32_23 (z : ℂ) :
    Matrix.submatrix (hingeMatrix32C z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (3 : Fin 6)) = minor32_23C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor32_23C (z : ℂ) : Matrix.det (minor32_23C z) = 4 * z - 3 := by
  unfold minor32_23C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-! ## §3. Cofactor closed forms (THEOREM; trace receipt values) -/

theorem cof32_d1 (z : ℂ) : cmCofactorC (hingeEdges32C z) 1 1 = 8 * z - 4 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_11, det_minor32LowerC,
    if_pos (by decide : Even ((1 : Fin 6).val + (1 : Fin 6).val))]
  ring

theorem cof32_d2 (z : ℂ) : cmCofactorC (hingeEdges32C z) 2 2 = 8 * z - 4 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_22, det_minor32LowerC,
    if_pos (by decide : Even ((2 : Fin 6).val + (2 : Fin 6).val))]
  ring

theorem cof32_d3 (z : ℂ) : cmCofactorC (hingeEdges32C z) 3 3 = 8 * z - 4 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_33, det_minor32LowerC,
    if_pos (by decide : Even ((3 : Fin 6).val + (3 : Fin 6).val))]
  ring

theorem cof32_d4 (z : ℂ) : cmCofactorC (hingeEdges32C z) 4 4 = 6 * z - 2 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_44, det_minorPPC,
    if_pos (by decide : Even ((4 : Fin 6).val + (4 : Fin 6).val))]
  ring

theorem cof32_d5 (z : ℂ) : cmCofactorC (hingeEdges32C z) 5 5 = 6 * z - 2 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_55, det_minorPPC,
    if_pos (by decide : Even ((5 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cof32_45 (z : ℂ) : cmCofactorC (hingeEdges32C z) 4 5 = 5 - 6 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_45, det_minor32_45C,
    if_neg (by decide : ¬ Even ((4 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cof32_14 (z : ℂ) : cmCofactorC (hingeEdges32C z) 1 4 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_14, det_minor32_14C,
    if_neg (by decide : ¬ Even ((1 : Fin 6).val + (4 : Fin 6).val))]
  ring

theorem cof32_15 (z : ℂ) : cmCofactorC (hingeEdges32C z) 1 5 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_15, det_minor32_15C,
    if_pos (by decide : Even ((1 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cof32_24 (z : ℂ) : cmCofactorC (hingeEdges32C z) 2 4 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_24, det_minor32_24C,
    if_pos (by decide : Even ((2 : Fin 6).val + (4 : Fin 6).val))]
  ring

theorem cof32_25 (z : ℂ) : cmCofactorC (hingeEdges32C z) 2 5 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_25, det_minor32_25C,
    if_neg (by decide : ¬ Even ((2 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cof32_34 (z : ℂ) : cmCofactorC (hingeEdges32C z) 3 4 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_34, det_minor32_34C,
    if_neg (by decide : ¬ Even ((3 : Fin 6).val + (4 : Fin 6).val))]
  ring

theorem cof32_35 (z : ℂ) : cmCofactorC (hingeEdges32C z) 3 5 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_35, det_minor32_35C,
    if_pos (by decide : Even ((3 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cof32_12 (z : ℂ) : cmCofactorC (hingeEdges32C z) 1 2 = 3 - 4 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_12, det_minor32_12C,
    if_neg (by decide : ¬ Even ((1 : Fin 6).val + (2 : Fin 6).val))]
  ring

theorem cof32_13 (z : ℂ) : cmCofactorC (hingeEdges32C z) 1 3 = 3 - 4 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_13, det_minor32_13C,
    if_pos (by decide : Even ((1 : Fin 6).val + (3 : Fin 6).val))]
  ring

theorem cof32_23 (z : ℂ) : cmCofactorC (hingeEdges32C z) 2 3 = 3 - 4 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges32, submatrix32_23, det_minor32_23C,
    if_neg (by decide : ¬ Even ((2 : Fin 6).val + (3 : Fin 6).val))]
  ring

/-! ## §4. The second denominator `8z - 4` never vanishes on the arc -/

/-- THEOREM: `8z - 4 = 0` iff `z = 1/2`, excluded on the unit circle
`|z| = 1` (the whole arc, endpoints included). -/
theorem denom32_ne (t : ℝ) : 8 * zArc t - 4 ≠ 0 := by
  intro h
  have h8 : (8 : ℂ) * zArc t = 4 := by linear_combination h
  have hns : Complex.normSq ((8 : ℂ) * zArc t) = Complex.normSq (4 : ℂ) := by
    rw [h8]
  rw [Complex.normSq_mul, normSq_zArc, mul_one, Complex.normSq_ofNat,
    Complex.normSq_ofNat] at hns
  norm_num at hns

/-! ## §5. The split-form cosine paths and the three hinge classes -/

/-- The split-form cosine path of the opposite pair `(p, q)` along the
physical threeTwo arc (MODEL). -/
noncomputable def threeTwoCosPath (p q : Fin 5) (t : ℝ) : ℂ :=
  dihedralCosSplitC (continuationEdgesC CausalPentType.threeTwo 1 1 t) p q

theorem threeTwoCosPath_symm (p q : Fin 5) :
    threeTwoCosPath q p = threeTwoCosPath p q :=
  funext fun _ => dihedralCosSplitC_symm _ p q

theorem threeTwoCosPath_apply_symm (p q : Fin 5) (t : ℝ) :
    threeTwoCosPath q p t = threeTwoCosPath p q t :=
  dihedralCosSplitC_symm _ p q

/-- Transport of the boundary-continuation package across the pair swap. -/
theorem boundary32_symm {p q : Fin 5}
    (h : ContinuousOn (threeTwoCosPath p q) (Set.Icc 0 1)
      ∧ threeTwoCosPath p q 1 = -(1 / 4 : ℂ)) :
    ContinuousOn (threeTwoCosPath q p) (Set.Icc 0 1)
      ∧ threeTwoCosPath q p 1 = -(1 / 4 : ℂ) := by
  rw [threeTwoCosPath_symm p q]
  exact h

/-! ### Class A: the spacelike hinge (0,1,2), opposite pair (3,4) -/

/-- THEOREM (class-A collapse): the split cosine of the spacelike hinge
collapses to `(5 - 6z)/(6z - 2)` everywhere on the arc. -/
theorem threeTwoCosPath_eq_spacelike (t : ℝ) :
    threeTwoCosPath 3 4 t = (5 - 6 * zArc t) / (6 * zArc t - 2) := by
  unfold threeTwoCosPath dihedralCosSplitC dihedralDenomSplitC
  rw [continuationEdgesC_physical32]
  have hv3 : cmVertexIndexC 3 = 4 := rfl
  have hv4 : cmVertexIndexC 4 = 5 := rfl
  rw [hv3, hv4, cof32_d4, cof32_d5, cof32_45, csqrt_mul_self (denom_ne t)]

/-- THEOREM (class-A branch certificate): branch regularity of the
spacelike hinge on the FULL open interior.  The Lorentzian ENDPOINT value
`-(11/8)` sits exactly ON the arccos cut (the classical boost angle); that
is an ALLOWED endpoint contact and is NOT part of this interior statement.
On the interior the cosine's imaginary part is
`-18 im z / normSq (6z - 2) ≠ 0`. -/
theorem branchRegular_threeTwo_spacelike :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      3 4 (Set.Ioo 0 1) := by
  intro t ht
  dsimp only
  have hy : 0 < (zArc t).im := zArc_im_pos ht
  have hv3 : cmVertexIndexC 3 = 4 := rfl
  have hv4 : cmVertexIndexC 4 = 5 := rfl
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
  · rw [hv3, continuationEdgesC_physical32, cof32_d4]
    exact hslit
  · rw [hv4, continuationEdgesC_physical32, cof32_d5]
    exact hslit
  · left
    have hcos : dihedralCosSplitC
        (continuationEdgesC CausalPentType.threeTwo 1 1 t) 3 4
        = (5 - 6 * zArc t) / (6 * zArc t - 2) :=
      threeTwoCosPath_eq_spacelike t
    rw [hcos]
    have hnum : (5 - 6 * zArc t).im * (6 * zArc t - 2).re
        - (5 - 6 * zArc t).re * (6 * zArc t - 2).im
        = -18 * (zArc t).im := by
      simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im,
        Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
      ring
    have hdiv : ((5 - 6 * zArc t) / (6 * zArc t - 2)).im
        = (-18 * (zArc t).im) / Complex.normSq (6 * zArc t - 2) := by
      rw [Complex.div_im, div_sub_div_same, hnum]
    rw [hdiv]
    apply div_ne_zero
    · exact ne_of_lt (mul_neg_of_neg_of_pos (by norm_num) hy)
    · exact (Complex.normSq_pos.mpr (denom_ne t)).ne'

/-- THEOREM (class-A boundary continuation): continuous on the CLOSED
interval; Lorentzian value `-(11/8)` (ON the arccos cut, allowed endpoint
contact, disclosed above); Euclidean value `-(1/4)`. -/
theorem boundary_threeTwo_spacelike :
    ContinuousOn (threeTwoCosPath 3 4) (Set.Icc 0 1)
      ∧ threeTwoCosPath 3 4 0 = -(11 / 8 : ℂ)
      ∧ threeTwoCosPath 3 4 1 = -(1 / 4 : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · have hmo : Continuous fun t => (5 - 6 * zArc t) / (6 * zArc t - 2) := by
      apply Continuous.div
      · exact continuous_const.sub (continuous_const.mul continuous_zArc)
      · exact (continuous_const.mul continuous_zArc).sub continuous_const
      · exact fun t => denom_ne t
    exact hmo.continuousOn.congr fun t _ => threeTwoCosPath_eq_spacelike t
  · rw [threeTwoCosPath_eq_spacelike 0, zArc_zero]
    norm_num
  · rw [threeTwoCosPath_eq_spacelike 1, zArc_one]
    norm_num

/-! ### Class B: the six mixed hinges (one lower, one upper vertex) -/

/-- THEOREM (class-B split form): with lower cofactor `8z - 4`, upper
cofactor `6z - 2`, numerator `-1`, the split cosine equals
`-1 / (csqrt (8z-4) * csqrt (6z-2))` everywhere on the arc.  No collapse
to a rational function: the two square roots have DIFFERENT arguments. -/
theorem threeTwoCosPath_eq_mixed (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 8 * z - 4)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 6 * z - 2)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC q) = -1) (t : ℝ) :
    threeTwoCosPath p q t
      = -1 / (csqrt (8 * zArc t - 4) * csqrt (6 * zArc t - 2)) := by
  unfold threeTwoCosPath dihedralCosSplitC dihedralDenomSplitC
  rw [continuationEdgesC_physical32, hpp, hqq, hpq]

/-- THEOREM (class-B branch certificate, parametric): both cofactors stay
in the open upper half-plane on the interior; each principal square root
lies in the open first quadrant, so their product has strictly positive
imaginary part and the cosine `-1/(s1*s2)` stays off the arccos cuts. -/
theorem branchRegular_threeTwo_mixed_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 8 * z - 4)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 6 * z - 2)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC q) = -1) :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      p q (Set.Ioo 0 1) := by
  intro t ht
  dsimp only
  have hy : 0 < (zArc t).im := zArc_im_pos ht
  have him8 : (8 * zArc t - 4).im = 8 * (zArc t).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have him6 : (6 * zArc t - 2).im = 6 * (zArc t).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have hup8 : 0 < (8 * zArc t - 4).im := by
    rw [him8]
    exact mul_pos (by norm_num : (0 : ℝ) < 8) hy
  have hup6 : 0 < (6 * zArc t - 2).im := by
    rw [him6]
    exact mul_pos (by norm_num : (0 : ℝ) < 6) hy
  refine ⟨?_, ?_, ?_⟩
  · rw [continuationEdgesC_physical32, hpp]
    exact Complex.mem_slitPlane_iff.mpr (Or.inr hup8.ne')
  · rw [continuationEdgesC_physical32, hqq]
    exact Complex.mem_slitPlane_iff.mpr (Or.inr hup6.ne')
  · left
    have hcos : dihedralCosSplitC
        (continuationEdgesC CausalPentType.threeTwo 1 1 t) p q
        = -1 / (csqrt (8 * zArc t - 4) * csqrt (6 * zArc t - 2)) :=
      threeTwoCosPath_eq_mixed p q hpp hqq hpq t
    rw [hcos]
    have hden : 0 < (csqrt (8 * zArc t - 4) * csqrt (6 * zArc t - 2)).im :=
      mul_im_pos_of_Q1 (csqrt_mem_Q1 hup8) (csqrt_mem_Q1 hup6)
    exact (neg_one_div_im_pos hden).ne'

/-- THEOREM (class-B boundary continuation, parametric): continuous on the
CLOSED interval (each square-root path continued across the Lorentzian
endpoint cut contact within the closed upper half-plane); Lorentzian value
`sqrt 6 / 24` (real; trace `+0.1020620726`), Euclidean value `-(1/4)`. -/
theorem boundary_threeTwo_mixed_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 8 * z - 4)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 6 * z - 2)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC q) = -1) :
    ContinuousOn (threeTwoCosPath p q) (Set.Icc 0 1)
      ∧ threeTwoCosPath p q 0 = ((Real.sqrt 6 / 24 : ℝ) : ℂ)
      ∧ threeTwoCosPath p q 1 = -(1 / 4 : ℂ) := by
  have heq := threeTwoCosPath_eq_mixed p q hpp hqq hpq
  have hw8 : Continuous fun t => 8 * zArc t - 4 :=
    (continuous_const.mul continuous_zArc).sub continuous_const
  have hw6 : Continuous fun t => 6 * zArc t - 2 :=
    (continuous_const.mul continuous_zArc).sub continuous_const
  have him8 : ∀ t : ℝ, (8 * zArc t - 4).im = 8 * (zArc t).im := by
    intro t
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have him6 : ∀ t : ℝ, (6 * zArc t - 2).im = 6 * (zArc t).im := by
    intro t
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hcs8 : ContinuousOn (fun t => csqrt (8 * zArc t - 4))
        (Set.Icc 0 1) := by
      apply continuousOn_csqrt_comp hw8 (fun t _ => denom32_ne t)
      intro t ht
      rw [him8]
      exact mul_nonneg (by norm_num) (zArc_im_nonneg ht)
    have hcs6 : ContinuousOn (fun t => csqrt (6 * zArc t - 2))
        (Set.Icc 0 1) := by
      apply continuousOn_csqrt_comp hw6 (fun t _ => denom_ne t)
      intro t ht
      rw [him6]
      exact mul_nonneg (by norm_num) (zArc_im_nonneg ht)
    have hdiv : ContinuousOn
        (fun t => -1 / (csqrt (8 * zArc t - 4) * csqrt (6 * zArc t - 2)))
        (Set.Icc 0 1) := by
      apply ContinuousOn.div continuousOn_const (hcs8.mul hcs6)
      intro t _
      exact mul_ne_zero (csqrt_ne_zero (denom32_ne t))
        (csqrt_ne_zero (denom_ne t))
    exact hdiv.congr fun t _ => heq t
  · rw [heq 0, zArc_zero]
    have h12 : (8 * (-1 : ℂ) - 4) = ((-12 : ℝ) : ℂ) := by norm_num
    have h8 : (6 * (-1 : ℂ) - 2) = ((-8 : ℝ) : ℂ) := by norm_num
    rw [h12, h8, csqrt_ofReal_neg (by norm_num : (-12 : ℝ) < 0),
      csqrt_ofReal_neg (by norm_num : (-8 : ℝ) < 0)]
    have h12' : Real.sqrt (-(-12 : ℝ)) = Real.sqrt 12 := by norm_num
    have h8' : Real.sqrt (-(-8 : ℝ)) = Real.sqrt 8 := by norm_num
    rw [h12', h8']
    have hr : Real.sqrt 12 * Real.sqrt 8 = 4 * Real.sqrt 6 := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12) 8,
        show (12 * 8 : ℝ) = 4 ^ 2 * 6 by norm_num,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (4 : ℝ) ^ 2) 6,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    have hrC : ((Real.sqrt 12 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ)
        = 4 * ((Real.sqrt 6 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hr]
      push_cast
      ring
    have hS6 : ((Real.sqrt 6 : ℝ) : ℂ) * ((Real.sqrt 6 : ℝ) : ℂ) = 6 := by
      rw [← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
      norm_num
    have hden : (((Real.sqrt 12 : ℝ) : ℂ) * Complex.I)
        * (((Real.sqrt 8 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ Complex.I_ne_zero)
        (mul_ne_zero ?_ Complex.I_ne_zero)
      · exact Complex.ofReal_ne_zero.mpr
          (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
      · exact Complex.ofReal_ne_zero.mpr
          (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    rw [div_eq_iff hden]
    push_cast
    linear_combination (((Real.sqrt 6 : ℝ) : ℂ) / 24) * hrC
      + (1 / 6 : ℂ) * hS6
      - ((((Real.sqrt 6 : ℝ) : ℂ) * ((Real.sqrt 12 : ℝ) : ℂ)
          * ((Real.sqrt 8 : ℝ) : ℂ)) / 24) * Complex.I_mul_I
  · rw [heq 1, zArc_one]
    have h4a : (8 * (1 : ℂ) - 4) = 4 := by norm_num
    have h4b : (6 * (1 : ℂ) - 2) = 4 := by norm_num
    rw [h4a, h4b, csqrt_four]
    norm_num

/-! ### Class C: the three upper-pair hinges (opposite pair in the lower
triple) -/

/-- THEOREM (class-C collapse): with both cofactors `8z - 4` and numerator
`3 - 4z`, the split cosine collapses to `(3 - 4z)/(8z - 4)` everywhere on
the arc. -/
theorem threeTwoCosPath_eq_upper (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 8 * z - 4)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 8 * z - 4)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC q) = 3 - 4 * z) (t : ℝ) :
    threeTwoCosPath p q t = (3 - 4 * zArc t) / (8 * zArc t - 4) := by
  unfold threeTwoCosPath dihedralCosSplitC dihedralDenomSplitC
  rw [continuationEdgesC_physical32, hpp, hqq, hpq,
    csqrt_mul_self (denom32_ne t)]

/-- THEOREM (class-C branch certificate, parametric): the cofactor
`8z - 4` stays in the open upper half-plane and the collapsed cosine has
imaginary part `-8 im z / normSq (8z - 4) ≠ 0` on the interior (trace
margin 0.4167, the worst interior-attained margin of the whole trace). -/
theorem branchRegular_threeTwo_upper_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 8 * z - 4)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 8 * z - 4)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC q) = 3 - 4 * z) :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      p q (Set.Ioo 0 1) := by
  intro t ht
  dsimp only
  have hy : 0 < (zArc t).im := zArc_im_pos ht
  have him8 : (8 * zArc t - 4).im = 8 * (zArc t).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have hslit : 8 * zArc t - 4 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    rw [him8]
    exact (mul_pos (by norm_num : (0 : ℝ) < 8) hy).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [continuationEdgesC_physical32, hpp]
    exact hslit
  · rw [continuationEdgesC_physical32, hqq]
    exact hslit
  · left
    have hcos : dihedralCosSplitC
        (continuationEdgesC CausalPentType.threeTwo 1 1 t) p q
        = (3 - 4 * zArc t) / (8 * zArc t - 4) :=
      threeTwoCosPath_eq_upper p q hpp hqq hpq t
    rw [hcos]
    have hnum : (3 - 4 * zArc t).im * (8 * zArc t - 4).re
        - (3 - 4 * zArc t).re * (8 * zArc t - 4).im
        = -8 * (zArc t).im := by
      simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im,
        Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
      ring
    have hdiv : ((3 - 4 * zArc t) / (8 * zArc t - 4)).im
        = (-8 * (zArc t).im) / Complex.normSq (8 * zArc t - 4) := by
      rw [Complex.div_im, div_sub_div_same, hnum]
    rw [hdiv]
    apply div_ne_zero
    · exact ne_of_lt (mul_neg_of_neg_of_pos (by norm_num) hy)
    · exact (Complex.normSq_pos.mpr (denom32_ne t)).ne'

/-- THEOREM (class-C boundary continuation, parametric): continuous on the
CLOSED interval; Lorentzian value `-(7/12)`, Euclidean value `-(1/4)`. -/
theorem boundary_threeTwo_upper_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 8 * z - 4)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 8 * z - 4)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdges32C z)
      (cmVertexIndexC p) (cmVertexIndexC q) = 3 - 4 * z) :
    ContinuousOn (threeTwoCosPath p q) (Set.Icc 0 1)
      ∧ threeTwoCosPath p q 0 = -(7 / 12 : ℂ)
      ∧ threeTwoCosPath p q 1 = -(1 / 4 : ℂ) := by
  have heq := threeTwoCosPath_eq_upper p q hpp hqq hpq
  refine ⟨?_, ?_, ?_⟩
  · have hmo : Continuous fun t => (3 - 4 * zArc t) / (8 * zArc t - 4) := by
      apply Continuous.div
      · exact continuous_const.sub (continuous_const.mul continuous_zArc)
      · exact (continuous_const.mul continuous_zArc).sub continuous_const
      · exact fun t => denom32_ne t
    exact hmo.continuousOn.congr fun t _ => heq t
  · rw [heq 0, zArc_zero]
    norm_num
  · rw [heq 1, zArc_one]
    norm_num

/-! ## §6. The ten instantiated hinges and the B2 headline -/

/-- Pair (0,3): mixed hinge (1,2,4). -/
theorem branchRegular32_pair03 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      0 3 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_mixed_pair 0 3 cof32_d1 cof32_d4 cof32_14

/-- Pair (0,4): mixed hinge (1,2,3). -/
theorem branchRegular32_pair04 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      0 4 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_mixed_pair 0 4 cof32_d1 cof32_d5 cof32_15

/-- Pair (1,3): mixed hinge (0,2,4). -/
theorem branchRegular32_pair13 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      1 3 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_mixed_pair 1 3 cof32_d2 cof32_d4 cof32_24

/-- Pair (1,4): mixed hinge (0,2,3). -/
theorem branchRegular32_pair14 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      1 4 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_mixed_pair 1 4 cof32_d2 cof32_d5 cof32_25

/-- Pair (2,3): mixed hinge (0,1,4). -/
theorem branchRegular32_pair23 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      2 3 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_mixed_pair 2 3 cof32_d3 cof32_d4 cof32_34

/-- Pair (2,4): mixed hinge (0,1,3). -/
theorem branchRegular32_pair24 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      2 4 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_mixed_pair 2 4 cof32_d3 cof32_d5 cof32_35

/-- Pair (0,1): upper-pair hinge (2,3,4). -/
theorem branchRegular32_pair01 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      0 1 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_upper_pair 0 1 cof32_d1 cof32_d2 cof32_12

/-- Pair (0,2): upper-pair hinge (1,3,4). -/
theorem branchRegular32_pair02 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      0 2 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_upper_pair 0 2 cof32_d1 cof32_d3 cof32_13

/-- Pair (1,2): upper-pair hinge (0,3,4). -/
theorem branchRegular32_pair12 :
    BranchRegularOn
      (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t)
      1 2 (Set.Ioo 0 1) :=
  branchRegular_threeTwo_upper_pair 1 2 cof32_d2 cof32_d3 cof32_23

theorem boundary32_pair03 :
    ContinuousOn (threeTwoCosPath 0 3) (Set.Icc 0 1)
      ∧ threeTwoCosPath 0 3 0 = ((Real.sqrt 6 / 24 : ℝ) : ℂ)
      ∧ threeTwoCosPath 0 3 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_mixed_pair 0 3 cof32_d1 cof32_d4 cof32_14

theorem boundary32_pair04 :
    ContinuousOn (threeTwoCosPath 0 4) (Set.Icc 0 1)
      ∧ threeTwoCosPath 0 4 0 = ((Real.sqrt 6 / 24 : ℝ) : ℂ)
      ∧ threeTwoCosPath 0 4 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_mixed_pair 0 4 cof32_d1 cof32_d5 cof32_15

theorem boundary32_pair13 :
    ContinuousOn (threeTwoCosPath 1 3) (Set.Icc 0 1)
      ∧ threeTwoCosPath 1 3 0 = ((Real.sqrt 6 / 24 : ℝ) : ℂ)
      ∧ threeTwoCosPath 1 3 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_mixed_pair 1 3 cof32_d2 cof32_d4 cof32_24

theorem boundary32_pair14 :
    ContinuousOn (threeTwoCosPath 1 4) (Set.Icc 0 1)
      ∧ threeTwoCosPath 1 4 0 = ((Real.sqrt 6 / 24 : ℝ) : ℂ)
      ∧ threeTwoCosPath 1 4 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_mixed_pair 1 4 cof32_d2 cof32_d5 cof32_25

theorem boundary32_pair23 :
    ContinuousOn (threeTwoCosPath 2 3) (Set.Icc 0 1)
      ∧ threeTwoCosPath 2 3 0 = ((Real.sqrt 6 / 24 : ℝ) : ℂ)
      ∧ threeTwoCosPath 2 3 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_mixed_pair 2 3 cof32_d3 cof32_d4 cof32_34

theorem boundary32_pair24 :
    ContinuousOn (threeTwoCosPath 2 4) (Set.Icc 0 1)
      ∧ threeTwoCosPath 2 4 0 = ((Real.sqrt 6 / 24 : ℝ) : ℂ)
      ∧ threeTwoCosPath 2 4 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_mixed_pair 2 4 cof32_d3 cof32_d5 cof32_35

theorem boundary32_pair01 :
    ContinuousOn (threeTwoCosPath 0 1) (Set.Icc 0 1)
      ∧ threeTwoCosPath 0 1 0 = -(7 / 12 : ℂ)
      ∧ threeTwoCosPath 0 1 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_upper_pair 0 1 cof32_d1 cof32_d2 cof32_12

theorem boundary32_pair02 :
    ContinuousOn (threeTwoCosPath 0 2) (Set.Icc 0 1)
      ∧ threeTwoCosPath 0 2 0 = -(7 / 12 : ℂ)
      ∧ threeTwoCosPath 0 2 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_upper_pair 0 2 cof32_d1 cof32_d3 cof32_13

theorem boundary32_pair12 :
    ContinuousOn (threeTwoCosPath 1 2) (Set.Icc 0 1)
      ∧ threeTwoCosPath 1 2 0 = -(7 / 12 : ℂ)
      ∧ threeTwoCosPath 1 2 1 = -(1 / 4 : ℂ) :=
  boundary_threeTwo_upper_pair 1 2 cof32_d2 cof32_d3 cof32_23

/-- THEOREM (B2 headline): for EVERY hinge of the threeTwo causal
4-simplex (1 spacelike + 6 mixed + 3 upper-pair; every unordered opposite
vertex pair, both orientations), at `a = 1`, `alpha = 1`:
(i) the split-form continuation is branch-regular on the FULL open arc
interior, and (ii) the split-form cosine path is continuous on the CLOSED
interval `[0,1]` and ends at the Euclidean regular-4-simplex value
`-(1/4)`.  The spacelike hinge's Lorentzian ENDPOINT sits ON the arccos
cut (allowed contact, disclosed in `branchRegular_threeTwo_spacelike`);
its branch certificate, like all the others, is interior-only. -/
theorem wick_continuation_threeTwo_hinges :
    ∀ p q : Fin 5, p ≠ q →
      BranchRegularOn
        (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t) p q
        (Set.Ioo 0 1)
      ∧ (ContinuousOn (threeTwoCosPath p q) (Set.Icc 0 1)
          ∧ threeTwoCosPath p q 1 = -(1 / 4 : ℂ)) := by
  intro p q hpq
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · exact ⟨branchRegular32_pair01,
      boundary32_pair01.1, boundary32_pair01.2.2⟩
  · exact ⟨branchRegular32_pair02,
      boundary32_pair02.1, boundary32_pair02.2.2⟩
  · exact ⟨branchRegular32_pair03,
      boundary32_pair03.1, boundary32_pair03.2.2⟩
  · exact ⟨branchRegular32_pair04,
      boundary32_pair04.1, boundary32_pair04.2.2⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair01,
      boundary32_symm ⟨boundary32_pair01.1, boundary32_pair01.2.2⟩⟩
  · exact absurd rfl hpq
  · exact ⟨branchRegular32_pair12,
      boundary32_pair12.1, boundary32_pair12.2.2⟩
  · exact ⟨branchRegular32_pair13,
      boundary32_pair13.1, boundary32_pair13.2.2⟩
  · exact ⟨branchRegular32_pair14,
      boundary32_pair14.1, boundary32_pair14.2.2⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair02,
      boundary32_symm ⟨boundary32_pair02.1, boundary32_pair02.2.2⟩⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair12,
      boundary32_symm ⟨boundary32_pair12.1, boundary32_pair12.2.2⟩⟩
  · exact absurd rfl hpq
  · exact ⟨branchRegular32_pair23,
      boundary32_pair23.1, boundary32_pair23.2.2⟩
  · exact ⟨branchRegular32_pair24,
      boundary32_pair24.1, boundary32_pair24.2.2⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair03,
      boundary32_symm ⟨boundary32_pair03.1, boundary32_pair03.2.2⟩⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair13,
      boundary32_symm ⟨boundary32_pair13.1, boundary32_pair13.2.2⟩⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair23,
      boundary32_symm ⟨boundary32_pair23.1, boundary32_pair23.2.2⟩⟩
  · exact absurd rfl hpq
  · exact ⟨branchRegular_threeTwo_spacelike,
      boundary_threeTwo_spacelike.1, boundary_threeTwo_spacelike.2.2⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair04,
      boundary32_symm ⟨boundary32_pair04.1, boundary32_pair04.2.2⟩⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair14,
      boundary32_symm ⟨boundary32_pair14.1, boundary32_pair14.2.2⟩⟩
  · exact ⟨branchRegularOn_symm branchRegular32_pair24,
      boundary32_symm ⟨boundary32_pair24.1, boundary32_pair24.2.2⟩⟩
  · exact ⟨branchRegularOn_symm branchRegular_threeTwo_spacelike,
      boundary32_symm ⟨boundary_threeTwo_spacelike.1,
        boundary_threeTwo_spacelike.2.2⟩⟩
  · exact absurd rfl hpq

/-! ## §7. Hinge areas-squared (THEOREM) -/

/-- THEOREM: threeTwo hinge areas-squared in closed form: the spacelike
hinge `(0,1,2)` has the constant `3/16`; every mixed hinge (shape
`(1, z, z)`) and every upper-pair hinge (shape `(z, z, 1)`) has
`z/4 - 1/16`.  Cut avoidance on the open interior is inherited verbatim
from `WickFourOneAllHinges.fourOne_areaSq_interior_off_cut` (same two
closed forms; the Lorentzian endpoint contact at `-5/16` is allowed). -/
theorem threeTwo_areaSq_closed (z : ℂ) :
    hingeAreaSqC (hingeEdges32C z) 0 1 2 = (3 / 16 : ℂ)
      ∧ hingeAreaSqC (hingeEdges32C z) 0 1 3 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 0 1 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 0 2 3 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 0 2 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 1 2 3 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 1 2 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 0 3 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 1 3 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdges32C z) 2 3 4 = z / 4 - 1 / 16 := by
  refine ⟨triangleAreaSqC_ones, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact triangleAreaSqC_one_z_z z
  · exact triangleAreaSqC_one_z_z z
  · exact triangleAreaSqC_one_z_z z
  · exact triangleAreaSqC_one_z_z z
  · exact triangleAreaSqC_one_z_z z
  · exact triangleAreaSqC_one_z_z z
  · exact triangleAreaSqC_z_z_one z
  · exact triangleAreaSqC_z_z_one z
  · exact triangleAreaSqC_z_z_one z

/-! ## §8. The two product-form kill certificates (gate FAIL events,
memorialized as kernel theorems) -/

/-- The exact interior crossing parameter of the mixed-class product form:
`tStarMixed = 1 - arccos(5/12)/pi ≈ 0.6368017686` (RESULTS.txt §3). -/
noncomputable def tStarMixed : ℝ := 1 - Real.arccos (5 / 12) / Real.pi

theorem tStarMixed_mem_Ioo : tStarMixed ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi := Real.pi_pos
  have h1 : 0 < Real.arccos (5 / 12) := Real.arccos_pos.mpr (by norm_num)
  have h2 : Real.arccos (5 / 12) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.mpr (by norm_num)
  constructor
  · have hle : Real.arccos (5 / 12) / Real.pi ≤ 1 / 2 := by
      rw [div_le_iff₀ hpi]
      linarith
    unfold tStarMixed
    linarith
  · have hgt : 0 < Real.arccos (5 / 12) / Real.pi := div_pos h1 hpi
    unfold tStarMixed
    linarith

theorem arg_tStarMixed :
    Real.pi * (1 - tStarMixed) = Real.arccos (5 / 12) := by
  have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold tStarMixed
  have h : (1 : ℝ) - (1 - Real.arccos (5 / 12) / Real.pi)
      = Real.arccos (5 / 12) / Real.pi := by ring
  rw [h, mul_comm, div_mul_cancel₀ _ hpne]

theorem cos_arg_tStarMixed :
    Real.cos (Real.pi * (1 - tStarMixed)) = 5 / 12 := by
  rw [arg_tStarMixed]
  exact Real.cos_arccos (by norm_num) (by norm_num)

/-- THEOREM (exact crossing value, mixed class): at `tStarMixed` the
product-form denominator argument `(8z - 4)(6z - 2)` equals `-40`
EXACTLY. -/
theorem product_form_crossing_value_mixed :
    (8 * zArc tStarMixed - 4) * (6 * zArc tStarMixed - 2) = -40 := by
  have hz : zArc tStarMixed = ((5 / 12 : ℝ) : ℂ)
      + ((Real.sin (Real.pi * (1 - tStarMixed)) : ℝ) : ℂ) * Complex.I := by
    rw [zArc_eq_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, cos_arg_tStarMixed]
  have h84 : 8 * zArc tStarMixed - 4
      = -(2 / 3 : ℂ)
        + 8 * ((Real.sin (Real.pi * (1 - tStarMixed)) : ℝ) : ℂ)
          * Complex.I := by
    rw [hz]
    push_cast
    ring
  have h62 : 6 * zArc tStarMixed - 2
      = (1 / 2 : ℂ)
        + 6 * ((Real.sin (Real.pi * (1 - tStarMixed)) : ℝ) : ℂ)
          * Complex.I := by
    rw [hz]
    push_cast
    ring
  have hprod : (8 * zArc tStarMixed - 4) * (6 * zArc tStarMixed - 2)
      = -(1 / 3 : ℂ)
        - 48 * ((Real.sin (Real.pi * (1 - tStarMixed)) : ℝ) : ℂ) ^ 2 := by
    rw [h84, h62]
    linear_combination
      (48 * ((Real.sin (Real.pi * (1 - tStarMixed)) : ℝ) : ℂ) ^ 2)
        * Complex.I_sq
  have hs2 : Real.sin (Real.pi * (1 - tStarMixed)) ^ 2 = 119 / 144 := by
    rw [Real.sin_sq, cos_arg_tStarMixed]
    norm_num
  have hcast : ((Real.sin (Real.pi * (1 - tStarMixed)) : ℝ) : ℂ) ^ 2
      = ((119 / 144 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hs2]
  rw [hprod, hcast]
  push_cast
  norm_num

/-- THEOREM (B2 kill certificate, mixed class): at the interior arc
parameter `tStarMixed ∈ (0,1)` the diagonal-cofactor product
`C_pp * C_qq = (8z-4)(6z-2)` of every mixed threeTwo hinge (here the
witness pair (0,3), CM rows 1 and 4, hinge `(1,2,4)`) equals `-40`
exactly, ON the `csqrt` branch cut (off `Complex.slitPlane`).  This KILLS
the single-sqrt product transcription `csqrt (C_pp * C_qq)` on the
threeTwo mixed class (RESULTS.txt §3: `Re z = 5/12`, value `-40`,
`t* ≈ 0.6368017686`). -/
theorem product_form_crossing_threeTwo_mixed :
    tStarMixed ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 tStarMixed) 1 1
          * cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 tStarMixed) 4 4
          = -40
      ∧ (-40 : ℂ) ∉ Complex.slitPlane := by
  refine ⟨tStarMixed_mem_Ioo, ?_, ?_⟩
  · rw [continuationEdgesC_physical32, cof32_d1, cof32_d4]
    exact product_form_crossing_value_mixed
  · intro hmem
    rw [Complex.mem_slitPlane_iff] at hmem
    simp at hmem
    linarith

/-- The upper-pair crossing parameter is `2/3` EXACTLY (the only crossing
of the whole trace with a rational parameter): `z(2/3) = exp(i pi/3)
= 1/2 + i sqrt 3 / 2`, `Re z = 1/2`. -/
theorem cos_arg_twoThirds :
    Real.cos (Real.pi * (1 - 2 / 3)) = 1 / 2 := by
  rw [show Real.pi * (1 - 2 / 3 : ℝ) = Real.pi / 3 by ring,
    Real.cos_pi_div_three]

/-- THEOREM (exact crossing value, upper-pair class): at `t = 2/3` the
product-form denominator argument `(8z - 4)^2 = 16 (2z - 1)^2` equals
`-48` EXACTLY. -/
theorem product_form_crossing_value_upper :
    (8 * zArc (2 / 3) - 4) * (8 * zArc (2 / 3) - 4) = -48 := by
  have hz : zArc (2 / 3) = ((1 / 2 : ℝ) : ℂ)
      + ((Real.sin (Real.pi * (1 - 2 / 3)) : ℝ) : ℂ) * Complex.I := by
    rw [zArc_eq_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, cos_arg_twoThirds]
  have h84 : 8 * zArc (2 / 3) - 4
      = 8 * ((Real.sin (Real.pi * (1 - 2 / 3)) : ℝ) : ℂ) * Complex.I := by
    rw [hz]
    push_cast
    ring
  have hprod : (8 * zArc (2 / 3) - 4) * (8 * zArc (2 / 3) - 4)
      = -(64 : ℂ) * ((Real.sin (Real.pi * (1 - 2 / 3)) : ℝ) : ℂ) ^ 2 := by
    rw [h84]
    linear_combination
      (64 * ((Real.sin (Real.pi * (1 - 2 / 3)) : ℝ) : ℂ) ^ 2)
        * Complex.I_sq
  have hs2 : Real.sin (Real.pi * (1 - 2 / 3)) ^ 2 = 3 / 4 := by
    rw [Real.sin_sq, cos_arg_twoThirds]
    norm_num
  have hcast : ((Real.sin (Real.pi * (1 - 2 / 3)) : ℝ) : ℂ) ^ 2
      = ((3 / 4 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hs2]
  rw [hprod, hcast]
  push_cast
  norm_num

/-- THEOREM (B2 kill certificate, upper-pair class): at the interior arc
parameter `t* = 2/3` EXACTLY, the diagonal-cofactor product
`C_pp * C_qq = (8z-4)^2` of every upper-pair threeTwo hinge (witness pair
(0,1), CM rows 1 and 2, hinge `(2,3,4)`) equals `-48` exactly, ON the
`csqrt` branch cut.  This KILLS the single-sqrt product transcription on
the threeTwo upper-pair class (RESULTS.txt §3: `Re z = 1/2`, value `-48`,
`t* = 2/3` exactly). -/
theorem product_form_crossing_threeTwo_upper :
    (2 / 3 : ℝ) ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 (2 / 3)) 1 1
          * cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 (2 / 3)) 2 2
          = -48
      ∧ (-48 : ℂ) ∉ Complex.slitPlane := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [continuationEdgesC_physical32, cof32_d1, cof32_d2]
    exact product_form_crossing_value_upper
  · intro hmem
    rw [Complex.mem_slitPlane_iff] at hmem
    simp at hmem
    linarith

/-! ## §9. Axiom audit

Expected for each: `[propext, Classical.choice, Quot.sound]`. -/

#print axioms wick_continuation_threeTwo_hinges
#print axioms branchRegular_threeTwo_spacelike
#print axioms boundary_threeTwo_spacelike
#print axioms threeTwo_areaSq_closed
#print axioms product_form_crossing_threeTwo_mixed
#print axioms product_form_crossing_threeTwo_upper

end WickThreeTwoHinges
end SevenGaps
end Gravity
end IndisputableMonolith

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

/-!
# All-Hinge Complex-First Wick Continuation of the (4,1) Causal 4-Simplex (Lane B1)

QG Seven-Gaps campaign, lane B of the finishing charter.  The landed module
`WickActionComplexFirst` certifies the split-form branch regularity and the
boundary continuation for ONE traced hinge of the fourOne causal 4-simplex
(triangle `(0,1,4)`, opposite pair `(2,3)`).  This module extends both
certificates to ALL TEN triangular hinges of the fourOne type, at the
physical point `a = 1`, `alpha = 1`, on the canonical upper-half-plane arc
`zArc` of `WickActionComplexFirst`.

## Hinge enumeration

A hinge of the 4-simplex on vertices `Fin 5` is an unordered triple; its
opposite pair is the complementary two vertices.  Enumerating hinges is
therefore enumerating unordered vertex pairs `{p, q}`.  For the fourOne
type (timelike edges exactly those touching the apex vertex 4,
`CausalSimplex4D.isTimelike`):

* opposite pair inside `{0,1,2,3}` (6 pairs): the hinge CONTAINS vertex 4
  and has 2 timelike triangle edges (the trace's timelike class); closed
  forms `C_pp = C_qq = 6z - 2`, `C_pq = 1 - 2z`, `areaSq = z/4 - 1/16`;
* opposite pair containing vertex 4 (4 pairs): the hinge avoids vertex 4
  and has 0 timelike triangle edges (the trace's spacelike class); closed
  forms `C_pp = 6z - 2` (the lower member), `C_qq = 4` (the apex),
  `C_pq = -1`, `areaSq = 3/16`.

All closed forms are kernel-checked below by explicit 5x5 minor
determinants (one per opposite pair), matching the executed trace receipt
(`state/qg_full_theory/wick_arc_trace/RESULTS.txt`, full per-hinge table).
Note the trace's summary section 3 swaps the two class COUNTS (it says
"6 spacelike / 4 timelike"); the per-hinge table and the combinatorics
(`C(4,3) = 4` triples avoiding vertex 4, `C(4,2) = 6` containing it) give
4 spacelike-class and 6 timelike-class hinges, and the table wins.

## What is proved

* `branchRegular_fourOne_allHinges`: for EVERY unordered opposite pair
  (equivalently every hinge), `BranchRegularOn` holds on the FULL open
  interior `Set.Ioo 0 1` of the physical arc.
* `wick_boundary_continuation_fourOne_allHinges`: every split-form cosine
  path is continuous on the CLOSED interval `[0,1]` and ends at the
  Euclidean regular-4-simplex value `-(1/4)`.
* `fourOne_lorentzian_endpoint_values`: the Lorentzian endpoint values:
  `-(3/8)` for every timelike-class hinge (the documented split-form sign
  factor of `WickActionComplexFirst.lorentzian_endpoint_sign_factor`), and
  the purely imaginary value `(sqrt 2 / 8) * I` for every spacelike-class
  hinge (the trace's `0 + 0.17677...j`, the imaginary Lorentzian dihedral
  datum at a spacelike hinge).
* `fourOne_areaSq_spacelike` / `fourOne_areaSq_timelike` /
  `fourOne_areaSq_interior_off_cut`: the ten hinge areas-squared in closed
  form and their sqrt-cut avoidance (constant `3/16` everywhere including
  endpoints; `z/4 - 1/16` on the open interior, with the ALLOWED Lorentzian
  endpoint contact at `-5/16` documented in the landed module).

## Honesty tiers

* MODEL: `fourOneCosPath` and the explicit minor matrices are definitional
  (complexifications inherited from `WickActionComplexFirst`; no new
  modeling choices).
* THEOREM: every declared theorem below is sorry-free and kernel-checked.
* OPEN: the action-level continuation (interior-hinge simplicial complex,
  deficit angles, the continued Regge action itself) is NOT claimed; it is
  the C12 lane's question.  No `FullTheoryLedger` flag is touched.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickFourOneAllHinges

open CausalSimplex4D
open WickActionComplexFirst

/-! ## §1. Generic principal-branch square-root lemmas (MODEL-level tools)

Mathlib (this pin) has no `Complex.sqrt`; `csqrt z = z ^ (1/2 : ℂ)` is the
landed principal-branch substitute (cut on `(-∞, 0]`).  The lemmas here are
the reusable analytic tools for every hinge class: non-vanishing, the open
first-quadrant image of the open upper half-plane, evaluation on positive
and negative reals, and continuity along paths confined to the CLOSED upper
half-plane minus the origin (the closed arc `[0,1]` maps there; the
Lorentzian endpoint sits ON the cut, which is exactly the boundary case the
within-set log continuity of Mathlib handles). -/

/-- THEOREM: `csqrt` never vanishes off the origin. -/
theorem csqrt_ne_zero {w : ℂ} (hw : w ≠ 0) : csqrt w ≠ 0 := by
  intro h
  unfold csqrt at h
  rw [Complex.cpow_eq_zero_iff] at h
  exact hw h.1

/-- THEOREM: the principal square root maps the open upper half-plane into
the open first quadrant (`arg w ∈ (0, π)` halves to `(0, π/2)`). -/
theorem csqrt_mem_Q1 {w : ℂ} (hw : 0 < w.im) :
    0 < (csqrt w).re ∧ 0 < (csqrt w).im := by
  have hne : w ≠ 0 := by
    intro h
    rw [h] at hw
    simp at hw
  have h12c : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have harg_pos : 0 < Complex.arg w := by
    rcases lt_or_eq_of_le (Complex.arg_nonneg_iff.mpr hw.le) with h | h
    · exact h
    · exfalso
      have h0 := Complex.arg_eq_zero_iff.mp h.symm
      exact absurd h0.2 (ne_of_gt hw)
  have harg_lt : Complex.arg w < Real.pi := by
    rcases lt_or_eq_of_le (Complex.arg_le_pi w) with h | h
    · exact h
    · exfalso
      have hpi := Complex.arg_eq_pi_iff.mp h
      exact absurd hpi.2 (ne_of_gt hw)
  have hcs : csqrt w = Complex.exp (Complex.log w * (1 / 2 : ℂ)) := by
    unfold csqrt
    rw [Complex.cpow_def_of_ne_zero hne]
  have him2 : (Complex.log w * (1 / 2 : ℂ)).im = Complex.arg w / 2 := by
    rw [h12c, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.log_im]
    ring
  rw [hcs]
  constructor
  · rw [Complex.exp_re, him2]
    refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · have := Real.pi_pos
      linarith
    · linarith
  · rw [Complex.exp_im, him2]
    refine mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi ?_ ?_)
    · linarith
    · have := Real.pi_pos
      linarith

/-- THEOREM: on nonnegative reals the principal square root is the real
square root. -/
theorem csqrt_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) :
    csqrt ((r : ℝ) : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  unfold csqrt
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num,
    ← Complex.ofReal_cpow hr, ← Real.sqrt_eq_rpow]

/-- THEOREM: `csqrt 4 = 2` (the constant apex cofactor of every
spacelike-class fourOne hinge). -/
theorem csqrt_four : csqrt 4 = 2 := by
  rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
    csqrt_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- THEOREM: on negative reals (approached within the closed upper
half-plane, the arc's Lorentzian endpoint case) the principal square root
is `sqrt (-r) * I` (`arg = π` halves to `π/2`). -/
theorem csqrt_ofReal_neg {r : ℝ} (hr : r < 0) :
    csqrt ((r : ℝ) : ℂ) = ((Real.sqrt (-r) : ℝ) : ℂ) * Complex.I := by
  have hne : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne
  have h12c : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hlog_re : (Complex.log ((r : ℝ) : ℂ)).re = Real.log (-r) := by
    rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hr]
  have hlog_im : (Complex.log ((r : ℝ) : ℂ)).im = Real.pi := by
    rw [Complex.log_im, Complex.arg_ofReal_of_neg hr]
  have hre2 : (Complex.log ((r : ℝ) : ℂ) * (1 / 2 : ℂ)).re
      = Real.log (-r) / 2 := by
    rw [h12c, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      hlog_re, hlog_im]
    ring
  have him2 : (Complex.log ((r : ℝ) : ℂ) * (1 / 2 : ℂ)).im
      = Real.pi / 2 := by
    rw [h12c, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      hlog_re, hlog_im]
    ring
  have hexp : Real.exp (Real.log (-r) / 2) = Real.sqrt (-r) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith : (0 : ℝ) < -r),
      mul_one_div]
  unfold csqrt
  rw [Complex.cpow_def_of_ne_zero hne]
  apply Complex.ext
  · rw [Complex.exp_re, hre2, him2, Real.cos_pi_div_two, mul_zero]
    simp [Complex.mul_re]
  · rw [Complex.exp_im, hre2, him2, Real.sin_pi_div_two, mul_one, hexp]
    simp [Complex.mul_im]

/-- THEOREM: the imaginary part of `-1/u` is strictly positive whenever
`im u > 0` (the arccos-cut avoidance workhorse for the mixed-denominator
hinge classes). -/
theorem neg_one_div_im_pos {u : ℂ} (hu : 0 < u.im) :
    0 < ((-1 : ℂ) / u).im := by
  have hne : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have h : ((-1 : ℂ) / u).im = u.im / Complex.normSq u := by
    rw [Complex.div_im]
    simp only [Complex.neg_im, Complex.one_im, Complex.neg_re,
      Complex.one_re, neg_zero]
    ring
  rw [h]
  exact div_pos hu (Complex.normSq_pos.mpr hne)

/-- THEOREM: products of open-first-quadrant numbers stay in the open upper
half-plane. -/
theorem mul_im_pos_of_Q1 {u v : ℂ} (hu : 0 < u.re ∧ 0 < u.im)
    (hv : 0 < v.re ∧ 0 < v.im) : 0 < (u * v).im := by
  rw [Complex.mul_im]
  exact add_pos (mul_pos hu.1 hv.2) (mul_pos hu.2 hv.1)

/-- THEOREM: the arc's imaginary part is nonnegative on the CLOSED interval
(`sin (π (1 - t)) ≥ 0` for `t ∈ [0, 1]`). -/
theorem zArc_im_nonneg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (zArc t).im := by
  rw [zArc_im]
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · exact mul_nonneg Real.pi_pos.le (by linarith [ht.2])
  · calc Real.pi * (1 - t) ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [ht.1]) Real.pi_pos.le
    _ = Real.pi := mul_one _

/-- THEOREM (path continuity of `csqrt` across the closed upper half-plane):
if a continuous path never vanishes on `[0,1]` and keeps a nonnegative
imaginary part there, then `csqrt` composed with it is continuous on the
CLOSED interval.  Off the cut this is the continuity of `cpow (1/2)` on
`Complex.slitPlane`; ON the cut (negative reals, the Lorentzian endpoint
case) it is Mathlib's one-sided log continuity within `{im ≥ 0}`
(`Complex.continuousWithinAt_log_of_re_neg_of_im_zero`). -/
theorem continuousOn_csqrt_comp {w : ℝ → ℂ} (hw : Continuous w)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, w t ≠ 0)
    (him : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (w t).im) :
    ContinuousOn (fun t => csqrt (w t)) (Set.Icc 0 1) := by
  intro t0 ht0
  unfold csqrt
  by_cases hs : w t0 ∈ Complex.slitPlane
  · have hc : ContinuousAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) (w t0) :=
      continuousAt_cpow_const hs
    exact (hc.comp hw.continuousAt).continuousWithinAt
  · have hne0 := hne t0 ht0
    rw [Complex.mem_slitPlane_iff] at hs
    push_neg at hs
    obtain ⟨hre_le, him0⟩ := hs
    have hre : (w t0).re < 0 := by
      rcases lt_or_eq_of_le hre_le with h | h
      · exact h
      · exfalso
        apply hne0
        apply Complex.ext
        · simpa using h
        · simpa using him0
    have hlog : ContinuousWithinAt Complex.log {z : ℂ | 0 ≤ z.im} (w t0) :=
      Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre him0
    have hg : ContinuousWithinAt
        (fun z : ℂ => Complex.exp (Complex.log z * (1 / 2 : ℂ)))
        {z : ℂ | 0 ≤ z.im} (w t0) :=
      Complex.continuous_exp.continuousAt.comp_continuousWithinAt
        (hlog.mul continuousWithinAt_const)
    have hcomp : ContinuousWithinAt
        (fun t => Complex.exp (Complex.log (w t) * (1 / 2 : ℂ)))
        (Set.Icc 0 1) t0 :=
      hg.comp hw.continuousWithinAt (fun t ht => him t ht)
    refine hcomp.congr (fun t ht => ?_) ?_
    · rw [Complex.cpow_def_of_ne_zero (hne t ht)]
    · rw [Complex.cpow_def_of_ne_zero hne0]

/-! ## §2. Cofactor symmetry (MODEL-level bookkeeping)

The complex CM matrix is symmetric, so `C_{rc} = C_{cr}` and the split-form
cosine is symmetric in its vertex pair.  This lets every hinge be certified
once, in a canonical pair orientation. -/

/-- THEOREM: the complex CM matrix is symmetric. -/
theorem cmMatrixC_symm (x : SqEdges10C) (i j : Fin 6) :
    cmMatrixC x j i = cmMatrixC x i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- THEOREM: minors of the symmetric CM matrix are symmetric in
(row, column). -/
theorem cmMinorC_symm (x : SqEdges10C) (r c : Fin 6) :
    cmMinorC x r c = cmMinorC x c r := by
  unfold cmMinorC
  rw [← Matrix.det_transpose
    (Matrix.submatrix (cmMatrixC x) (Fin.succAbove c) (Fin.succAbove r))]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
  exact cmMatrixC_symm x (Fin.succAbove c j) (Fin.succAbove r i)

/-- THEOREM: cofactors of the symmetric CM matrix are symmetric. -/
theorem cmCofactorC_symm (x : SqEdges10C) (r c : Fin 6) :
    cmCofactorC x r c = cmCofactorC x c r := by
  unfold cmCofactorC cmCofactorSignC
  rw [cmMinorC_symm, Nat.add_comm r.val c.val]

/-- THEOREM: the split-form cosine is symmetric in the opposite pair. -/
theorem dihedralCosSplitC_symm (x : SqEdges10C) (p q : Fin 5) :
    dihedralCosSplitC x q p = dihedralCosSplitC x p q := by
  unfold dihedralCosSplitC dihedralDenomSplitC
  rw [cmCofactorC_symm, mul_comm]

/-- THEOREM: branch regularity is symmetric in the opposite pair. -/
theorem branchRegularOn_symm {x : ℝ → SqEdges10C} {p q : Fin 5} {s : Set ℝ}
    (h : BranchRegularOn x p q s) : BranchRegularOn x q p s := by
  intro t ht
  obtain ⟨h1, h2, h3⟩ := h t ht
  refine ⟨h2, h1, ?_⟩
  rw [dihedralCosSplitC_symm]
  exact h3

/-! ## §3. Per-pair 5x5 minors of the fourOne matrix (kernel-checked)

`hingeMatrixC` (landed) is the bordered 6x6 complex CM matrix of the
fourOne tuple at spacelike value 1, timelike value `z`.  Each opposite
vertex pair `(p, q)` needs the minors at CM rows/columns `(p+1, q+1)`.
The landed module covers CM `(3,3)`, `(4,4)`, `(3,4)`; everything else is
built here explicitly and evaluated with the landed heavy-simp pattern.
Every determinant below was cross-checked against exact sympy expansion
before formalization. -/

/-- The diagonal minor deleting CM row/col 1 (vertex 0) equals the landed
`minorPPC` matrix (vertices 0..3 are interchangeable in the fourOne
tuple). -/
theorem submatrix41_11 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (1 : Fin 6)) = minorPPC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Diagonal minor at CM row/col 2 (vertex 1), again `minorPPC`. -/
theorem submatrix41_22 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (2 : Fin 6)) = minorPPC z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The apex diagonal minor (delete CM row/col 5, vertex 4): the regular
unit tetrahedron CM matrix. -/
def minor41_55C : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 2, 2 => 0
    | 3, 3 => 0
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix41_55 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (5 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor41_55C := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
/-- THEOREM (symbolic 5x5 determinant): the apex diagonal minor is the
regular unit tetrahedron value 4 (`C_qq = 4`, trace constant). -/
theorem det_minor41_55C : Matrix.det minor41_55C = 4 := by
  unfold minor41_55C
  -- Style note: bare `simp` retained deliberately, mirroring the proved
  -- pattern of `WickActionComplexFirst.det_minorPPC`.
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

/-- Off-diagonal minor at CM (1,2) (opposite pair (0,1)). -/
def minor41_12C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 4 => z
    | 2, 2 => 0
    | 2, 4 => z
    | 3, 3 => 0
    | 3, 4 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix41_12 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (2 : Fin 6)) = minor41_12C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_12C (z : ℂ) : Matrix.det (minor41_12C z) = 2 * z - 1 := by
  unfold minor41_12C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Off-diagonal minor at CM (1,3) (opposite pair (0,2)). -/
def minor41_13C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 2 => 0
    | 1, 4 => z
    | 2, 4 => z
    | 3, 3 => 0
    | 3, 4 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix41_13 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (3 : Fin 6)) = minor41_13C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_13C (z : ℂ) : Matrix.det (minor41_13C z) = 1 - 2 * z := by
  unfold minor41_13C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Off-diagonal minor at CM (1,4) (opposite pair (0,3)). -/
def minor41_14C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 2 => 0
    | 1, 4 => z
    | 2, 3 => 0
    | 2, 4 => z
    | 3, 4 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix41_14 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minor41_14C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_14C (z : ℂ) : Matrix.det (minor41_14C z) = 2 * z - 1 := by
  unfold minor41_14C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Off-diagonal minor at CM (2,3) (opposite pair (1,2)). -/
def minor41_23C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 4 => z
    | 2, 4 => z
    | 3, 3 => 0
    | 3, 4 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix41_23 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (3 : Fin 6)) = minor41_23C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_23C (z : ℂ) : Matrix.det (minor41_23C z) = 2 * z - 1 := by
  unfold minor41_23C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Off-diagonal minor at CM (2,4) (opposite pair (1,3)). -/
def minor41_24C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 1, 4 => z
    | 2, 3 => 0
    | 2, 4 => z
    | 3, 4 => z
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => 0
    | _, _ => 1

theorem submatrix41_24 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (4 : Fin 6)) = minor41_24C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_24C (z : ℂ) : Matrix.det (minor41_24C z) = 1 - 2 * z := by
  unfold minor41_24C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Spacelike-class off-diagonal minor at CM (1,5) (opposite pair (0,4)). -/
def minor41_15C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 2 => 0
    | 2, 3 => 0
    | 3, 4 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => z
    | _, _ => 1

theorem submatrix41_15 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (1 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor41_15C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_15C (z : ℂ) : Matrix.det (minor41_15C z) = -1 := by
  unfold minor41_15C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Spacelike-class off-diagonal minor at CM (2,5) (opposite pair (1,4)). -/
def minor41_25C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 2, 3 => 0
    | 3, 4 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => z
    | _, _ => 1

theorem submatrix41_25 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (2 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor41_25C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_25C (z : ℂ) : Matrix.det (minor41_25C z) = 1 := by
  unfold minor41_25C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Spacelike-class off-diagonal minor at CM (3,5) (opposite pair (2,4)). -/
def minor41_35C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 2, 2 => 0
    | 3, 4 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => z
    | _, _ => 1

theorem submatrix41_35 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (3 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor41_35C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_35C (z : ℂ) : Matrix.det (minor41_35C z) = -1 := by
  unfold minor41_35C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- Spacelike-class off-diagonal minor at CM (4,5) (opposite pair (3,4)). -/
def minor41_45C (z : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    match i.val, j.val with
    | 0, 0 => 0
    | 1, 1 => 0
    | 2, 2 => 0
    | 3, 3 => 0
    | 4, 1 => z
    | 4, 2 => z
    | 4, 3 => z
    | 4, 4 => z
    | _, _ => 1

theorem submatrix41_45 (z : ℂ) :
    Matrix.submatrix (hingeMatrixC z) (Fin.succAbove (4 : Fin 6))
      (Fin.succAbove (5 : Fin 6)) = minor41_45C z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
theorem det_minor41_45C (z : ℂ) : Matrix.det (minor41_45C z) = 1 := by
  unfold minor41_45C
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-! ## §4. Cofactor closed forms per CM index pair (THEOREM)

Trace receipt closed forms: diagonal cofactors `6z - 2` at CM 1..4 and `4`
at CM 5; off-diagonal `1 - 2z` inside CM 1..4 and `-1` against CM 5. -/

theorem cofactor41_d1 (z : ℂ) : cmCofactorC (hingeEdgesC z) 1 1 = 6 * z - 2 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_11, det_minorPPC,
    if_pos (by decide : Even ((1 : Fin 6).val + (1 : Fin 6).val))]
  ring

theorem cofactor41_d2 (z : ℂ) : cmCofactorC (hingeEdgesC z) 2 2 = 6 * z - 2 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_22, det_minorPPC,
    if_pos (by decide : Even ((2 : Fin 6).val + (2 : Fin 6).val))]
  ring

theorem cofactor41_d5 (z : ℂ) : cmCofactorC (hingeEdgesC z) 5 5 = 4 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_55, det_minor41_55C,
    if_pos (by decide : Even ((5 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cofactor41_12 (z : ℂ) : cmCofactorC (hingeEdgesC z) 1 2 = 1 - 2 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_12, det_minor41_12C,
    if_neg (by decide : ¬ Even ((1 : Fin 6).val + (2 : Fin 6).val))]
  ring

theorem cofactor41_13 (z : ℂ) : cmCofactorC (hingeEdgesC z) 1 3 = 1 - 2 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_13, det_minor41_13C,
    if_pos (by decide : Even ((1 : Fin 6).val + (3 : Fin 6).val))]
  ring

theorem cofactor41_14 (z : ℂ) : cmCofactorC (hingeEdgesC z) 1 4 = 1 - 2 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_14, det_minor41_14C,
    if_neg (by decide : ¬ Even ((1 : Fin 6).val + (4 : Fin 6).val))]
  ring

theorem cofactor41_23 (z : ℂ) : cmCofactorC (hingeEdgesC z) 2 3 = 1 - 2 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_23, det_minor41_23C,
    if_neg (by decide : ¬ Even ((2 : Fin 6).val + (3 : Fin 6).val))]
  ring

theorem cofactor41_24 (z : ℂ) : cmCofactorC (hingeEdgesC z) 2 4 = 1 - 2 * z := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_24, det_minor41_24C,
    if_pos (by decide : Even ((2 : Fin 6).val + (4 : Fin 6).val))]
  ring

theorem cofactor41_15 (z : ℂ) : cmCofactorC (hingeEdgesC z) 1 5 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_15, det_minor41_15C,
    if_pos (by decide : Even ((1 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cofactor41_25 (z : ℂ) : cmCofactorC (hingeEdgesC z) 2 5 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_25, det_minor41_25C,
    if_neg (by decide : ¬ Even ((2 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cofactor41_35 (z : ℂ) : cmCofactorC (hingeEdgesC z) 3 5 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_35, det_minor41_35C,
    if_pos (by decide : Even ((3 : Fin 6).val + (5 : Fin 6).val))]
  ring

theorem cofactor41_45 (z : ℂ) : cmCofactorC (hingeEdgesC z) 4 5 = -1 := by
  unfold cmCofactorC cmCofactorSignC cmMinorC
  rw [cmMatrixC_hingeEdges, submatrix41_45, det_minor41_45C,
    if_neg (by decide : ¬ Even ((4 : Fin 6).val + (5 : Fin 6).val))]
  ring

/-! ## §5. The two hinge classes, parametrically (THEOREM) -/

/-- The split-form cosine path of the opposite pair `(p, q)` along the
physical fourOne arc (MODEL; generalizes the landed `hingeCosPath`, which
is the case `p = 2`, `q = 3`). -/
noncomputable def fourOneCosPath (p q : Fin 5) (t : ℝ) : ℂ :=
  dihedralCosSplitC (continuationEdgesC CausalPentType.fourOne 1 1 t) p q

theorem fourOneCosPath_symm (p q : Fin 5) :
    fourOneCosPath q p = fourOneCosPath p q :=
  funext fun _ => dihedralCosSplitC_symm _ p q

theorem fourOneCosPath_apply_symm (p q : Fin 5) (t : ℝ) :
    fourOneCosPath q p t = fourOneCosPath p q t :=
  dihedralCosSplitC_symm _ p q

/-- Transport of the boundary-continuation package across the pair swap. -/
theorem boundary_symm {p q : Fin 5}
    (h : ContinuousOn (fourOneCosPath p q) (Set.Icc 0 1)
      ∧ fourOneCosPath p q 1 = -(1 / 4 : ℂ)) :
    ContinuousOn (fourOneCosPath q p) (Set.Icc 0 1)
      ∧ fourOneCosPath q p 1 = -(1 / 4 : ℂ) := by
  rw [fourOneCosPath_symm p q]
  exact h

/-- THEOREM (timelike-class collapse): with both diagonal cofactors
`6z - 2` and numerator `1 - 2z`, the split cosine collapses to the cut-free
rational function everywhere on the arc. -/
theorem fourOneCosPath_eq_timelike (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 6 * z - 2)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 6 * z - 2)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC q) = 1 - 2 * z) (t : ℝ) :
    fourOneCosPath p q t = (1 - 2 * zArc t) / (6 * zArc t - 2) := by
  unfold fourOneCosPath dihedralCosSplitC dihedralDenomSplitC
  rw [continuationEdgesC_physical, hpp, hqq, hpq, csqrt_mul_self (denom_ne t)]

/-- THEOREM (spacelike-class collapse): with diagonal cofactors `6z - 2`
and `4` and numerator `-1`, the split cosine is `-1 / (csqrt (6z-2) * 2)`
everywhere on the arc. -/
theorem fourOneCosPath_eq_spacelike (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 6 * z - 2)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 4)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC q) = -1) (t : ℝ) :
    fourOneCosPath p q t = -1 / (csqrt (6 * zArc t - 2) * 2) := by
  unfold fourOneCosPath dihedralCosSplitC dihedralDenomSplitC
  rw [continuationEdgesC_physical, hpp, hqq, hpq, csqrt_four]

/-- THEOREM (timelike-class branch certificate, parametric): full open
interior, exactly the landed single-hinge argument. -/
theorem branchRegular_fourOne_timelike_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 6 * z - 2)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 6 * z - 2)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC q) = 1 - 2 * z) :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      p q (Set.Ioo 0 1) := by
  intro t ht
  dsimp only
  have hy : 0 < (zArc t).im := zArc_im_pos ht
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
  · rw [continuationEdgesC_physical, hpp]
    exact hslit
  · rw [continuationEdgesC_physical, hqq]
    exact hslit
  · left
    have hcos : dihedralCosSplitC
        (continuationEdgesC CausalPentType.fourOne 1 1 t) p q
        = (1 - 2 * zArc t) / (6 * zArc t - 2) :=
      fourOneCosPath_eq_timelike p q hpp hqq hpq t
    rw [hcos]
    have hnum : (1 - 2 * zArc t).im * (6 * zArc t - 2).re
        - (1 - 2 * zArc t).re * (6 * zArc t - 2).im = -2 * (zArc t).im := by
      simp only [Complex.sub_im, Complex.sub_re, Complex.mul_im,
        Complex.mul_re, Complex.one_im, Complex.one_re, Complex.re_ofNat,
        Complex.im_ofNat]
      ring
    have hdiv : ((1 - 2 * zArc t) / (6 * zArc t - 2)).im
        = (-2 * (zArc t).im) / Complex.normSq (6 * zArc t - 2) := by
      rw [Complex.div_im, div_sub_div_same, hnum]
    rw [hdiv]
    apply div_ne_zero
    · exact ne_of_lt (mul_neg_of_neg_of_pos (by norm_num) hy)
    · exact (Complex.normSq_pos.mpr (denom_ne t)).ne'

/-- THEOREM (spacelike-class branch certificate, parametric): the apex
cofactor is the positive constant 4 (trivially off the cut), the lower
cofactor stays in the open upper half-plane, and the cosine
`-1 / (csqrt (6z-2) * 2)` has strictly positive imaginary part on the
interior because `csqrt (6z-2)` lies in the open first quadrant. -/
theorem branchRegular_fourOne_spacelike_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 6 * z - 2)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 4)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC q) = -1) :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      p q (Set.Ioo 0 1) := by
  intro t ht
  dsimp only
  have hy : 0 < (zArc t).im := zArc_im_pos ht
  have him6 : (6 * zArc t - 2).im = 6 * (zArc t).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  have hup : 0 < (6 * zArc t - 2).im := by
    rw [him6]
    exact mul_pos (by norm_num : (0 : ℝ) < 6) hy
  refine ⟨?_, ?_, ?_⟩
  · rw [continuationEdgesC_physical, hpp]
    exact Complex.mem_slitPlane_iff.mpr (Or.inr hup.ne')
  · rw [continuationEdgesC_physical, hqq]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  · left
    have hcos : dihedralCosSplitC
        (continuationEdgesC CausalPentType.fourOne 1 1 t) p q
        = -1 / (csqrt (6 * zArc t - 2) * 2) :=
      fourOneCosPath_eq_spacelike p q hpp hqq hpq t
    rw [hcos]
    have hq1 := csqrt_mem_Q1 hup
    have hden : 0 < (csqrt (6 * zArc t - 2) * 2).im := by
      rw [Complex.mul_im]
      simp only [Complex.re_ofNat, Complex.im_ofNat, mul_zero, zero_add]
      linarith [hq1.2]
    exact (neg_one_div_im_pos hden).ne'

/-- THEOREM (timelike-class boundary continuation, parametric):
continuous on the CLOSED interval, Lorentzian value `-(3/8)`, Euclidean
value `-(1/4)`. -/
theorem boundary_fourOne_timelike_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 6 * z - 2)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 6 * z - 2)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC q) = 1 - 2 * z) :
    ContinuousOn (fourOneCosPath p q) (Set.Icc 0 1)
      ∧ fourOneCosPath p q 0 = -(3 / 8 : ℂ)
      ∧ fourOneCosPath p q 1 = -(1 / 4 : ℂ) := by
  have heq := fourOneCosPath_eq_timelike p q hpp hqq hpq
  refine ⟨?_, ?_, ?_⟩
  · have hmo : Continuous fun t => (1 - 2 * zArc t) / (6 * zArc t - 2) := by
      apply Continuous.div
      · exact continuous_const.sub (continuous_const.mul continuous_zArc)
      · exact (continuous_const.mul continuous_zArc).sub continuous_const
      · exact fun t => denom_ne t
    exact hmo.continuousOn.congr fun t _ => heq t
  · rw [heq 0, zArc_zero]
    norm_num
  · rw [heq 1, zArc_one]
    norm_num

/-- THEOREM (spacelike-class boundary continuation, parametric):
continuous on the CLOSED interval (via the closed-upper-half-plane
continuity of `csqrt` along the arc; the Lorentzian endpoint has the
cofactor `-8` ON the cut boundary, an allowed endpoint contact), Lorentzian
value `(sqrt 2 / 8) * I` (purely imaginary), Euclidean value `-(1/4)`. -/
theorem boundary_fourOne_spacelike_pair (p q : Fin 5)
    (hpp : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC p) = 6 * z - 2)
    (hqq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC q) (cmVertexIndexC q) = 4)
    (hpq : ∀ z : ℂ, cmCofactorC (hingeEdgesC z)
      (cmVertexIndexC p) (cmVertexIndexC q) = -1) :
    ContinuousOn (fourOneCosPath p q) (Set.Icc 0 1)
      ∧ fourOneCosPath p q 0 = ((Real.sqrt 2 / 8 : ℝ) : ℂ) * Complex.I
      ∧ fourOneCosPath p q 1 = -(1 / 4 : ℂ) := by
  have heq := fourOneCosPath_eq_spacelike p q hpp hqq hpq
  have hwcont : Continuous fun t => 6 * zArc t - 2 :=
    (continuous_const.mul continuous_zArc).sub continuous_const
  have him6 : ∀ t : ℝ, (6 * zArc t - 2).im = 6 * (zArc t).im := by
    intro t
    simp only [Complex.sub_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat]
    ring
  refine ⟨?_, ?_, ?_⟩
  · have hcs : ContinuousOn (fun t => csqrt (6 * zArc t - 2))
        (Set.Icc 0 1) := by
      apply continuousOn_csqrt_comp hwcont (fun t _ => denom_ne t)
      intro t ht
      rw [him6]
      exact mul_nonneg (by norm_num) (zArc_im_nonneg ht)
    have hdiv : ContinuousOn (fun t => -1 / (csqrt (6 * zArc t - 2) * 2))
        (Set.Icc 0 1) := by
      apply ContinuousOn.div continuousOn_const (hcs.mul continuousOn_const)
      intro t _
      exact mul_ne_zero (csqrt_ne_zero (denom_ne t)) two_ne_zero
    exact hdiv.congr fun t _ => heq t
  · rw [heq 0, zArc_zero]
    have h8 : (6 * (-1 : ℂ) - 2) = ((-8 : ℝ) : ℂ) := by norm_num
    rw [h8, csqrt_ofReal_neg (by norm_num : (-8 : ℝ) < 0)]
    have h82 : Real.sqrt (-(-8 : ℝ)) = 2 * Real.sqrt 2 := by
      rw [show -(-8 : ℝ) = 2 ^ 2 * 2 by norm_num,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ (2 : ℝ) ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h82]
    have hS : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
      rw [← Complex.ofReal_mul,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hden : (((2 * Real.sqrt 2 : ℝ) : ℂ) * Complex.I) * 2 ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero ?_ Complex.I_ne_zero) two_ne_zero
      exact Complex.ofReal_ne_zero.mpr
        (ne_of_gt (mul_pos two_pos (Real.sqrt_pos.mpr (by norm_num))))
    rw [div_eq_iff hden]
    push_cast
    linear_combination (-(Complex.I * Complex.I) / 2) * hS
      - Complex.I_mul_I
  · rw [heq 1, zArc_one]
    have h4 : (6 * (1 : ℂ) - 2) = 4 := by norm_num
    rw [h4, csqrt_four]
    norm_num

/-! ## §6. The ten instantiated hinges and the all-hinge headlines -/

/-- Pair (0,1): hinge (2,3,4), timelike class. -/
theorem branchRegular_pair01 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      0 1 (Set.Ioo 0 1) :=
  branchRegular_fourOne_timelike_pair 0 1 cofactor41_d1 cofactor41_d2
    cofactor41_12

/-- Pair (0,2): hinge (1,3,4), timelike class. -/
theorem branchRegular_pair02 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      0 2 (Set.Ioo 0 1) :=
  branchRegular_fourOne_timelike_pair 0 2 cofactor41_d1 cofactor_pp
    cofactor41_13

/-- Pair (0,3): hinge (1,2,4), timelike class. -/
theorem branchRegular_pair03 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      0 3 (Set.Ioo 0 1) :=
  branchRegular_fourOne_timelike_pair 0 3 cofactor41_d1 cofactor_qq
    cofactor41_14

/-- Pair (1,2): hinge (0,3,4), timelike class. -/
theorem branchRegular_pair12 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      1 2 (Set.Ioo 0 1) :=
  branchRegular_fourOne_timelike_pair 1 2 cofactor41_d2 cofactor_pp
    cofactor41_23

/-- Pair (1,3): hinge (0,2,4), timelike class. -/
theorem branchRegular_pair13 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      1 3 (Set.Ioo 0 1) :=
  branchRegular_fourOne_timelike_pair 1 3 cofactor41_d2 cofactor_qq
    cofactor41_24

/-- Pair (2,3): hinge (0,1,4), the landed traced hinge. -/
theorem branchRegular_pair23 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      2 3 (Set.Ioo 0 1) :=
  branchRegular_fourOne_timelike_pair 2 3 cofactor_pp cofactor_qq cofactor_pq

/-- Pair (0,4): hinge (1,2,3), spacelike class. -/
theorem branchRegular_pair04 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      0 4 (Set.Ioo 0 1) :=
  branchRegular_fourOne_spacelike_pair 0 4 cofactor41_d1 cofactor41_d5
    cofactor41_15

/-- Pair (1,4): hinge (0,2,3), spacelike class. -/
theorem branchRegular_pair14 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      1 4 (Set.Ioo 0 1) :=
  branchRegular_fourOne_spacelike_pair 1 4 cofactor41_d2 cofactor41_d5
    cofactor41_25

/-- Pair (2,4): hinge (0,1,3), spacelike class. -/
theorem branchRegular_pair24 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      2 4 (Set.Ioo 0 1) :=
  branchRegular_fourOne_spacelike_pair 2 4 cofactor_pp cofactor41_d5
    cofactor41_35

/-- Pair (3,4): hinge (0,1,2), spacelike class. -/
theorem branchRegular_pair34 :
    BranchRegularOn (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t)
      3 4 (Set.Ioo 0 1) :=
  branchRegular_fourOne_spacelike_pair 3 4 cofactor_qq cofactor41_d5
    cofactor41_45

/-- THEOREM (B1 headline, branch certificates): for EVERY hinge of the
fourOne causal 4-simplex (every unordered opposite vertex pair, both
orientations), the split-form continuation is branch-regular on the FULL
open arc interior at the physical point `a = 1`, `alpha = 1`.  The ten
hinges: (0,1,2)|(3,4), (0,1,3)|(2,4), (0,1,4)|(2,3), (0,2,3)|(1,4),
(0,2,4)|(1,3), (0,3,4)|(1,2), (1,2,3)|(0,4), (1,2,4)|(0,3),
(1,3,4)|(0,2), (2,3,4)|(0,1). -/
theorem branchRegular_fourOne_allHinges :
    ∀ p q : Fin 5, p ≠ q →
      BranchRegularOn
        (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t) p q
        (Set.Ioo 0 1) := by
  intro p q hpq
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · exact branchRegular_pair01
  · exact branchRegular_pair02
  · exact branchRegular_pair03
  · exact branchRegular_pair04
  · exact branchRegularOn_symm branchRegular_pair01
  · exact absurd rfl hpq
  · exact branchRegular_pair12
  · exact branchRegular_pair13
  · exact branchRegular_pair14
  · exact branchRegularOn_symm branchRegular_pair02
  · exact branchRegularOn_symm branchRegular_pair12
  · exact absurd rfl hpq
  · exact branchRegular_pair23
  · exact branchRegular_pair24
  · exact branchRegularOn_symm branchRegular_pair03
  · exact branchRegularOn_symm branchRegular_pair13
  · exact branchRegularOn_symm branchRegular_pair23
  · exact absurd rfl hpq
  · exact branchRegular_pair34
  · exact branchRegularOn_symm branchRegular_pair04
  · exact branchRegularOn_symm branchRegular_pair14
  · exact branchRegularOn_symm branchRegular_pair24
  · exact branchRegularOn_symm branchRegular_pair34
  · exact absurd rfl hpq

theorem boundary_pair01 :
    ContinuousOn (fourOneCosPath 0 1) (Set.Icc 0 1)
      ∧ fourOneCosPath 0 1 0 = -(3 / 8 : ℂ)
      ∧ fourOneCosPath 0 1 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_timelike_pair 0 1 cofactor41_d1 cofactor41_d2 cofactor41_12

theorem boundary_pair02 :
    ContinuousOn (fourOneCosPath 0 2) (Set.Icc 0 1)
      ∧ fourOneCosPath 0 2 0 = -(3 / 8 : ℂ)
      ∧ fourOneCosPath 0 2 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_timelike_pair 0 2 cofactor41_d1 cofactor_pp cofactor41_13

theorem boundary_pair03 :
    ContinuousOn (fourOneCosPath 0 3) (Set.Icc 0 1)
      ∧ fourOneCosPath 0 3 0 = -(3 / 8 : ℂ)
      ∧ fourOneCosPath 0 3 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_timelike_pair 0 3 cofactor41_d1 cofactor_qq cofactor41_14

theorem boundary_pair12 :
    ContinuousOn (fourOneCosPath 1 2) (Set.Icc 0 1)
      ∧ fourOneCosPath 1 2 0 = -(3 / 8 : ℂ)
      ∧ fourOneCosPath 1 2 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_timelike_pair 1 2 cofactor41_d2 cofactor_pp cofactor41_23

theorem boundary_pair13 :
    ContinuousOn (fourOneCosPath 1 3) (Set.Icc 0 1)
      ∧ fourOneCosPath 1 3 0 = -(3 / 8 : ℂ)
      ∧ fourOneCosPath 1 3 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_timelike_pair 1 3 cofactor41_d2 cofactor_qq cofactor41_24

theorem boundary_pair23 :
    ContinuousOn (fourOneCosPath 2 3) (Set.Icc 0 1)
      ∧ fourOneCosPath 2 3 0 = -(3 / 8 : ℂ)
      ∧ fourOneCosPath 2 3 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_timelike_pair 2 3 cofactor_pp cofactor_qq cofactor_pq

theorem boundary_pair04 :
    ContinuousOn (fourOneCosPath 0 4) (Set.Icc 0 1)
      ∧ fourOneCosPath 0 4 0 = ((Real.sqrt 2 / 8 : ℝ) : ℂ) * Complex.I
      ∧ fourOneCosPath 0 4 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_spacelike_pair 0 4 cofactor41_d1 cofactor41_d5 cofactor41_15

theorem boundary_pair14 :
    ContinuousOn (fourOneCosPath 1 4) (Set.Icc 0 1)
      ∧ fourOneCosPath 1 4 0 = ((Real.sqrt 2 / 8 : ℝ) : ℂ) * Complex.I
      ∧ fourOneCosPath 1 4 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_spacelike_pair 1 4 cofactor41_d2 cofactor41_d5 cofactor41_25

theorem boundary_pair24 :
    ContinuousOn (fourOneCosPath 2 4) (Set.Icc 0 1)
      ∧ fourOneCosPath 2 4 0 = ((Real.sqrt 2 / 8 : ℝ) : ℂ) * Complex.I
      ∧ fourOneCosPath 2 4 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_spacelike_pair 2 4 cofactor_pp cofactor41_d5 cofactor41_35

theorem boundary_pair34 :
    ContinuousOn (fourOneCosPath 3 4) (Set.Icc 0 1)
      ∧ fourOneCosPath 3 4 0 = ((Real.sqrt 2 / 8 : ℝ) : ℂ) * Complex.I
      ∧ fourOneCosPath 3 4 1 = -(1 / 4 : ℂ) :=
  boundary_fourOne_spacelike_pair 3 4 cofactor_qq cofactor41_d5 cofactor41_45

/-- THEOREM (B1 headline, boundary continuation): every split-form cosine
path of the fourOne type is continuous on the CLOSED interval `[0, 1]` and
ends at the Euclidean regular-4-simplex value `-(1/4)` (`+C_pq` numerator
convention of the landed module; textbook `-C` interior cosine `+1/4`). -/
theorem wick_boundary_continuation_fourOne_allHinges :
    ∀ p q : Fin 5, p ≠ q →
      ContinuousOn (fourOneCosPath p q) (Set.Icc 0 1)
        ∧ fourOneCosPath p q 1 = -(1 / 4 : ℂ) := by
  intro p q hpq
  fin_cases p <;> fin_cases q
  · exact absurd rfl hpq
  · exact ⟨boundary_pair01.1, boundary_pair01.2.2⟩
  · exact ⟨boundary_pair02.1, boundary_pair02.2.2⟩
  · exact ⟨boundary_pair03.1, boundary_pair03.2.2⟩
  · exact ⟨boundary_pair04.1, boundary_pair04.2.2⟩
  · exact boundary_symm ⟨boundary_pair01.1, boundary_pair01.2.2⟩
  · exact absurd rfl hpq
  · exact ⟨boundary_pair12.1, boundary_pair12.2.2⟩
  · exact ⟨boundary_pair13.1, boundary_pair13.2.2⟩
  · exact ⟨boundary_pair14.1, boundary_pair14.2.2⟩
  · exact boundary_symm ⟨boundary_pair02.1, boundary_pair02.2.2⟩
  · exact boundary_symm ⟨boundary_pair12.1, boundary_pair12.2.2⟩
  · exact absurd rfl hpq
  · exact ⟨boundary_pair23.1, boundary_pair23.2.2⟩
  · exact ⟨boundary_pair24.1, boundary_pair24.2.2⟩
  · exact boundary_symm ⟨boundary_pair03.1, boundary_pair03.2.2⟩
  · exact boundary_symm ⟨boundary_pair13.1, boundary_pair13.2.2⟩
  · exact boundary_symm ⟨boundary_pair23.1, boundary_pair23.2.2⟩
  · exact absurd rfl hpq
  · exact ⟨boundary_pair34.1, boundary_pair34.2.2⟩
  · exact boundary_symm ⟨boundary_pair04.1, boundary_pair04.2.2⟩
  · exact boundary_symm ⟨boundary_pair14.1, boundary_pair14.2.2⟩
  · exact boundary_symm ⟨boundary_pair24.1, boundary_pair24.2.2⟩
  · exact boundary_symm ⟨boundary_pair34.1, boundary_pair34.2.2⟩
  · exact absurd rfl hpq

/-- THEOREM (B1 headline, Lorentzian endpoint values): the split-form value
at `t = 0` is `-(3/8)` for every timelike-class hinge (opposite pair inside
`{0,1,2,3}`; the documented sign factor of the landed module applies) and
the purely imaginary `(sqrt 2 / 8) * I` for every spacelike-class hinge
(opposite pair containing the apex).  No unrestricted equality with the
real Lorentzian formula is claimed. -/
theorem fourOne_lorentzian_endpoint_values :
    (∀ p q : Fin 5, p ≠ q → p ≠ 4 → q ≠ 4 →
        fourOneCosPath p q 0 = -(3 / 8 : ℂ))
      ∧ (∀ p : Fin 5, p ≠ 4 →
        fourOneCosPath p 4 0 = ((Real.sqrt 2 / 8 : ℝ) : ℂ) * Complex.I
          ∧ fourOneCosPath 4 p 0
            = ((Real.sqrt 2 / 8 : ℝ) : ℂ) * Complex.I) := by
  constructor
  · intro p q hpq hp4 hq4
    fin_cases p <;> fin_cases q
    · exact absurd rfl hpq
    · exact boundary_pair01.2.1
    · exact boundary_pair02.2.1
    · exact boundary_pair03.2.1
    · exact absurd rfl hq4
    · exact (fourOneCosPath_apply_symm 0 1 0).trans boundary_pair01.2.1
    · exact absurd rfl hpq
    · exact boundary_pair12.2.1
    · exact boundary_pair13.2.1
    · exact absurd rfl hq4
    · exact (fourOneCosPath_apply_symm 0 2 0).trans boundary_pair02.2.1
    · exact (fourOneCosPath_apply_symm 1 2 0).trans boundary_pair12.2.1
    · exact absurd rfl hpq
    · exact boundary_pair23.2.1
    · exact absurd rfl hq4
    · exact (fourOneCosPath_apply_symm 0 3 0).trans boundary_pair03.2.1
    · exact (fourOneCosPath_apply_symm 1 3 0).trans boundary_pair13.2.1
    · exact (fourOneCosPath_apply_symm 2 3 0).trans boundary_pair23.2.1
    · exact absurd rfl hpq
    · exact absurd rfl hq4
    · exact absurd rfl hp4
    · exact absurd rfl hp4
    · exact absurd rfl hp4
    · exact absurd rfl hp4
    · exact absurd rfl hp4
  · intro p hp4
    fin_cases p
    · exact ⟨boundary_pair04.2.1,
        (fourOneCosPath_apply_symm 0 4 0).trans boundary_pair04.2.1⟩
    · exact ⟨boundary_pair14.2.1,
        (fourOneCosPath_apply_symm 1 4 0).trans boundary_pair14.2.1⟩
    · exact ⟨boundary_pair24.2.1,
        (fourOneCosPath_apply_symm 2 4 0).trans boundary_pair24.2.1⟩
    · exact ⟨boundary_pair34.2.1,
        (fourOneCosPath_apply_symm 3 4 0).trans boundary_pair34.2.1⟩
    · exact absurd rfl hp4

/-! ## §7. Hinge areas-squared: closed forms and cut avoidance (THEOREM)

The remaining hinge datum.  Two triangle shapes occur (`(1, z, z)` for
timelike-class hinges and `(1, 1, 1)` for spacelike-class hinges); the
`(z, z, 1)` shape is proved here as well for the threeTwo module. -/

set_option maxHeartbeats 2000000 in
/-- THEOREM (4x4 symbolic determinant): `triangleAreaSqC 1 z z
= z/4 - 1/16` (the timelike-class hinge shape). -/
theorem triangleAreaSqC_one_z_z (z : ℂ) :
    triangleAreaSqC 1 z z = z / 4 - 1 / 16 := by
  unfold triangleAreaSqC triCMMatrixC
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

set_option maxHeartbeats 2000000 in
/-- THEOREM (4x4 symbolic determinant): `triangleAreaSqC z z 1
= z/4 - 1/16` (the threeTwo upper-pair hinge shape). -/
theorem triangleAreaSqC_z_z_one (z : ℂ) :
    triangleAreaSqC z z 1 = z / 4 - 1 / 16 := by
  unfold triangleAreaSqC triCMMatrixC
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

set_option maxHeartbeats 2000000 in
/-- THEOREM (4x4 symbolic determinant): the regular unit triangle,
`triangleAreaSqC 1 1 1 = 3/16`. -/
theorem triangleAreaSqC_ones : triangleAreaSqC 1 1 1 = (3 / 16 : ℂ) := by
  unfold triangleAreaSqC triCMMatrixC
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

/-- THEOREM: closed forms of the four spacelike-class fourOne hinge
areas-squared: constant `3/16` (all three triangle edges spacelike). -/
theorem fourOne_areaSq_spacelike (z : ℂ) :
    hingeAreaSqC (hingeEdgesC z) 0 1 2 = (3 / 16 : ℂ)
      ∧ hingeAreaSqC (hingeEdgesC z) 0 1 3 = (3 / 16 : ℂ)
      ∧ hingeAreaSqC (hingeEdgesC z) 0 2 3 = (3 / 16 : ℂ)
      ∧ hingeAreaSqC (hingeEdgesC z) 1 2 3 = (3 / 16 : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact triangleAreaSqC_ones

/-- THEOREM: closed forms of the six timelike-class fourOne hinge
areas-squared: `z/4 - 1/16` (one spacelike edge, two timelike edges to the
apex).  The landed `hingeAreaSqC_closed` is the (0,1,4) case. -/
theorem fourOne_areaSq_timelike (z : ℂ) :
    hingeAreaSqC (hingeEdgesC z) 0 1 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdgesC z) 0 2 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdgesC z) 0 3 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdgesC z) 1 2 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdgesC z) 1 3 4 = z / 4 - 1 / 16
      ∧ hingeAreaSqC (hingeEdgesC z) 2 3 4 = z / 4 - 1 / 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact triangleAreaSqC_one_z_z z

/-- THEOREM: the constant spacelike-class area-squared `3/16` avoids the
sqrt cut EVERYWHERE (both endpoints included), and the timelike-class
area-squared `z/4 - 1/16` avoids it on the full open interior (its
Lorentzian endpoint value `-5/16` sits ON the cut boundary, the ALLOWED
endpoint contact documented in the landed module). -/
theorem fourOne_areaSq_interior_off_cut {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ((3 / 16 : ℂ) ∈ Complex.slitPlane)
      ∧ (zArc t / 4 - 1 / 16 ∈ Complex.slitPlane) := by
  constructor
  · exact Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  · apply Complex.mem_slitPlane_iff.mpr
    right
    have hy : 0 < (zArc t).im := zArc_im_pos ht
    have him : (zArc t / 4 - 1 / 16).im = (zArc t).im / 4 := by
      simp only [Complex.sub_im, Complex.div_ofNat_im, Complex.one_im]
      ring
    rw [him]
    exact (div_pos hy (by norm_num : (0 : ℝ) < 4)).ne'

/-! ## §8. Axiom audit

Expected for each: `[propext, Classical.choice, Quot.sound]`. -/

#print axioms branchRegular_fourOne_allHinges
#print axioms wick_boundary_continuation_fourOne_allHinges
#print axioms fourOne_lorentzian_endpoint_values
#print axioms fourOne_areaSq_spacelike
#print axioms fourOne_areaSq_timelike
#print axioms fourOne_areaSq_interior_off_cut

end WickFourOneAllHinges
end SevenGaps
end Gravity
end IndisputableMonolith

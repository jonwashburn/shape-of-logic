import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import IndisputableMonolith.Geometry.CayleyMengerN

/-!
# Causal (CDT) 4-Simplex Classes and the Kinematical Wick Rotation (4D)

QG Seven-Gaps campaign, Lorentzian-sector lane, Phase 3a: the 4D Lorentzian
lift of the kernel-checked 3D causal-simplex machinery in
`Gravity.SevenGaps.CausalSimplexWick` (conventions mirrored in prose; this
module is import-independent of it).  This module builds:

1. the causal (CDT-style) 4-simplex classes in D = 4, with the
   spacelike/timelike edge-type assignment verified combinatorially from the
   slice structure (decide-able lemmas);
2. the Wick rotation as an explicit map on the ten squared edge lengths,
   proved to be an involution and proved to act on the causal class as the
   algebraic continuation `alpha ↦ -alpha`;
3. the 4-simplex Cayley-Menger determinant `cm4`, grounded in the existing
   dimension-parametric `Geometry.CayleyMengerN.cmDetN` (the bordered 6x6
   determinant), evaluated exactly on both causal classes;
4. the exact Euclidean non-degeneracy thresholds in `alpha` for both types
   (in the cm4-positivity criterion), with degeneracy exactly at threshold
   and strict cm4 negativity on the Lorentzian side.

## Conventions (4D CDT, Ambjorn-Jurkiewicz-Loll)

Spatial slices are 3D triangulated manifolds of equilateral tetrahedra with
squared edge length `a^2`.  Spacetime between slices `t` and `t+1` is filled
by two 4-simplex types:

* type (4,1): four vertices on slice `t`, one on slice `t+1`
  (6 spacelike + 4 timelike edges); the time-reflected type (1,4) has the
  same edge-length multiset and is covered by the same theorems;
* type (3,2): three vertices on slice `t`, two on slice `t+1`
  (3 + 1 = 4 spacelike + 6 timelike edges); the reflection (2,3) likewise.

Spacelike edges carry squared length `a^2`; timelike edges carry squared
length `-alpha * a^2` in the Lorentzian regime, `alpha > 0`.  The Wick
rotation flips the sign of the timelike squared lengths, i.e. it is the
continuation `alpha ↦ -alpha` on the causal class.

Vertex/edge indexing: vertices `0,1,2,3,4`; the ten edges are ordered
lexicographically,

  edge 0 = (0,1), edge 1 = (0,2), edge 2 = (0,3), edge 3 = (0,4),
  edge 4 = (1,2), edge 5 = (1,3), edge 6 = (1,4),
  edge 7 = (2,3), edge 8 = (2,4), edge 9 = (3,4).

Slice assignment: for (4,1) vertices `{0,1,2,3}` lie on slice `t` and `4` on
slice `t+1` (timelike edges `{3,6,8,9}`); for (3,2) vertices `{0,1,2}` lie
on slice `t` and `{3,4}` on slice `t+1` (timelike edges `{2,3,5,6,7,8}`,
spacelike edges `{0,1,4,9}`).

## Derived thresholds (symbolic determinant evaluation, certified below)

`cm4 x := -(cmDetN of the bordered 6x6 CM matrix)`, normalized so that
`simplexVolumeSqN = cm4 / 9216` identically (proved below); on genuinely
embeddable 4-simplices this formal expression is the classical `V^2`.
Sanity anchor: regular unit 4-simplex `cm4 = 5` (classically
V = sqrt 5 / 96, so 9216 V^2 = 5).

Evaluated on the Euclideanized causal tuples:

* type (4,1): `cm4 = (8*alpha - 3) * a^8`, hence non-degenerate exactly for
  `alpha > 3/8` (`alphaMin fourOne = 3/8`); cross-check: the AJL volume
  `V(4,1) = (a^4/96) * sqrt (8*alpha - 3)` gives `9216 V^2 = (8*alpha-3) a^8`;
* type (3,2): `cm4 = (12*alpha - 7) * a^8`, hence non-degenerate exactly for
  `alpha > 7/12` (`alphaMin threeTwo = 7/12`); cross-check:
  `V(3,2) = (a^4/96) * sqrt (12*alpha - 7)` gives `9216 V^2 = (12*alpha-7) a^8`.

Both types are simultaneously non-degenerate exactly for `alpha > 7/12`, the
standard 4d CDT Euclidean-regime bound.  Degeneracy at threshold is proved
(`cm4 = 0` at `alpha = alphaMin`), so the range is exact.  On the Lorentzian
side `cm4 = -(8*alpha + 3) * a^8` (type (4,1)) and `-(12*alpha + 7) * a^8`
(type (3,2)): strictly negative for all `alpha >= 0`.  What is proved is the
cm4 sign fact; the classical equivalence "cm4 > 0 iff embeddable in R^4"
(which upgrades cm4 negativity to non-realizability) is NOT formalized in
this repo for n = 4 (the 3D case has `Geometry/TetrahedronRealization.lean`;
no 4D analog exists yet).  Under that classical reading the Lorentzian
tuples are never Euclidean-realizable and the Wick rotation is genuinely
required.  At the physical point `alpha = 1` both types reduce to the
regular 4-simplex tuple, `cm4 = 5 * a^8`.

## Honesty tiers

* THEOREM: every declared theorem in this file is proved with zero sorry,
  zero admit, zero new axioms; hypotheses are explicit (`0 < a`,
  `alphaMin ty < alpha`, etc.).  Exception: `causalSimplex4DStatus_flags`
  is a documentation record of hand-set booleans, not a mathematical
  theorem; it is not counted in this tier.
* MODEL: `CausalPentType`, `sliceOf`, `isTimelike`, `lorentzianSqEdges`,
  `euclideanSqEdges`, `wick`, `alphaMin`, `NonDegeneratePent` are
  definitional encodings of the standard 4d CDT conventions.  "cm4 > 0" is
  used throughout as the non-degeneracy criterion; its classical
  equivalence to embeddability in R^4 is not formalized here.
* OPEN: (a) the 4D Cayley-Menger realizability theorem (cm4 > 0 iff
  embeddable in R^4; 3D analog in `Geometry/TetrahedronRealization.lean`);
  (b) the action-level Lorentzian continuation in 4D (complex dihedral
  angles at timelike triangular hinges, the boost/sinh sector of the 4d
  Regge action, and the continuation of the action itself), which is wave
  3b and is deliberately not attempted here; see `CausalSimplex4DStatus`.

## decide usage (all on finite Bool-valued data, none on `ℝ`)

`isTimelike_fourOne_eq_crossSlice`, `isTimelike_threeTwo_eq_crossSlice`,
`slice_count_fourOne`, `slice_count_threeTwo`, `timelike_count_fourOne`,
`spacelike_count_fourOne`, `timelike_count_threeTwo`,
`spacelike_count_threeTwo`.  No `native_decide` anywhere.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace CausalSimplex4D

open Geometry.CayleyMengerN

/-! ## §1. The causal 4-simplex classes (combinatorial layer)

MODEL: the two 4d CDT 4-simplex types and their slice structure. -/

/-- The two causal 4-simplex types of 4d CDT between adjacent slices.
`fourOne` has four vertices on slice `t` and one on slice `t+1` (its time
reflection (1,4) has the same edge data); `threeTwo` has three vertices on
slice `t` and two on slice `t+1` (reflection (2,3) likewise). -/
inductive CausalPentType
  | fourOne
  | threeTwo

/-- Squared edge lengths of a 4-simplex, indexed by `Fin 10`
(lexicographic edge order, see module docstring). -/
abbrev SqEdges10 : Type := Fin 10 → ℝ

/-- Edge index → vertex pair for the 4-simplex on vertices `Fin 5`:
edges `(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)` in
lexicographic order. -/
def pentEdgeVertices : Fin 10 → Fin 5 × Fin 5
  | 0 => (0, 1)
  | 1 => (0, 2)
  | 2 => (0, 3)
  | 3 => (0, 4)
  | 4 => (1, 2)
  | 5 => (1, 3)
  | 6 => (1, 4)
  | 7 => (2, 3)
  | 8 => (2, 4)
  | 9 => (3, 4)

/-- Slice membership of each vertex (`false` = slice `t`, `true` = slice
`t+1`).  For (4,1): vertices `0,1,2,3` on slice `t`, vertex `4` on `t+1`.
For (3,2): vertices `0,1,2` on slice `t`, vertices `3,4` on `t+1`. -/
def sliceOf : CausalPentType → Fin 5 → Bool
  | CausalPentType.fourOne, v => v.val == 4
  | CausalPentType.threeTwo, v => (v.val == 3) || (v.val == 4)

/-- Edge-type assignment: `true` iff the edge is timelike (connects the two
slices).  For (4,1) the timelike edges are `{3,6,8,9}` (those touching the
apex vertex 4); for (3,2) they are `{2,3,5,6,7,8}` (the six cross edges). -/
def isTimelike : CausalPentType → Fin 10 → Bool
  | CausalPentType.fourOne, e =>
      (e.val == 3) || (e.val == 6) || (e.val == 8) || (e.val == 9)
  | CausalPentType.threeTwo, e =>
      (e.val == 2) || (e.val == 3) || (e.val == 5)
        || (e.val == 6) || (e.val == 7) || (e.val == 8)

/-- THEOREM (by `decide`): for type (4,1), an edge is timelike iff its two
endpoints (via `pentEdgeVertices`) lie on different slices.  This verifies
the edge-type table against the slice structure. -/
theorem isTimelike_fourOne_eq_crossSlice :
    ∀ e : Fin 10,
      isTimelike CausalPentType.fourOne e
        = (sliceOf CausalPentType.fourOne (pentEdgeVertices e).1
            != sliceOf CausalPentType.fourOne (pentEdgeVertices e).2) := by
  decide

/-- THEOREM (by `decide`): same cross-slice verification for type (3,2). -/
theorem isTimelike_threeTwo_eq_crossSlice :
    ∀ e : Fin 10,
      isTimelike CausalPentType.threeTwo e
        = (sliceOf CausalPentType.threeTwo (pentEdgeVertices e).1
            != sliceOf CausalPentType.threeTwo (pentEdgeVertices e).2) := by
  decide

/-- THEOREM (by `decide`): type (4,1) has 4 vertices on slice `t` and 1 on
slice `t+1`. -/
theorem slice_count_fourOne :
    (Finset.univ.filter fun v : Fin 5 =>
        sliceOf CausalPentType.fourOne v = false).card = 4
      ∧ (Finset.univ.filter fun v : Fin 5 =>
        sliceOf CausalPentType.fourOne v = true).card = 1 := by
  decide

/-- THEOREM (by `decide`): type (3,2) has 3 vertices on slice `t` and 2 on
slice `t+1`. -/
theorem slice_count_threeTwo :
    (Finset.univ.filter fun v : Fin 5 =>
        sliceOf CausalPentType.threeTwo v = false).card = 3
      ∧ (Finset.univ.filter fun v : Fin 5 =>
        sliceOf CausalPentType.threeTwo v = true).card = 2 := by
  decide

/-- THEOREM (by `decide`): type (4,1) has exactly 4 timelike edges. -/
theorem timelike_count_fourOne :
    (Finset.univ.filter fun e : Fin 10 =>
      isTimelike CausalPentType.fourOne e = true).card = 4 := by
  decide

/-- THEOREM (by `decide`): type (4,1) has exactly 6 spacelike edges. -/
theorem spacelike_count_fourOne :
    (Finset.univ.filter fun e : Fin 10 =>
      isTimelike CausalPentType.fourOne e = false).card = 6 := by
  decide

/-- THEOREM (by `decide`): type (3,2) has exactly 6 timelike edges. -/
theorem timelike_count_threeTwo :
    (Finset.univ.filter fun e : Fin 10 =>
      isTimelike CausalPentType.threeTwo e = true).card = 6 := by
  decide

/-- THEOREM (by `decide`): type (3,2) has exactly 4 spacelike edges
(3 within the lower slice triangle plus 1 within the upper slice pair). -/
theorem spacelike_count_threeTwo :
    (Finset.univ.filter fun e : Fin 10 =>
      isTimelike CausalPentType.threeTwo e = false).card = 4 := by
  decide

noncomputable section

/-! ## §2. Lorentzian and Euclideanized squared-edge tuples

MODEL: the standard 4d CDT edge-length assignments. -/

/-- Lorentzian squared-edge tuple: spacelike edges carry `a^2`, timelike
edges carry `-(alpha * a^2)`. -/
def lorentzianSqEdges (ty : CausalPentType) (a alpha : ℝ) : SqEdges10 :=
  fun e => if isTimelike ty e then -(alpha * a ^ 2) else a ^ 2

/-- Euclideanized squared-edge tuple: spacelike edges carry `a^2`, timelike
edges carry `+alpha * a^2` (the image of the Lorentzian tuple under the Wick
map, equivalently the continuation `alpha ↦ -alpha`). -/
def euclideanSqEdges (ty : CausalPentType) (a alpha : ℝ) : SqEdges10 :=
  fun e => if isTimelike ty e then alpha * a ^ 2 else a ^ 2

/-- The Lorentzian causal class: all Lorentzian tuples of the given type
with positive lattice spacing and positive asymmetry `alpha`. -/
def LorentzianClass (ty : CausalPentType) : Set SqEdges10 :=
  { x | ∃ a alpha : ℝ, 0 < a ∧ 0 < alpha ∧ x = lorentzianSqEdges ty a alpha }

/-- THEOREM: all entries of the Euclideanized tuple are positive when
`0 < a` and `0 < alpha`. -/
theorem euclideanSqEdges_pos (ty : CausalPentType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : 0 < alpha) (e : Fin 10) :
    0 < euclideanSqEdges ty a alpha e := by
  have h2 : 0 < a ^ 2 := pow_pos ha 2
  unfold euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h]
    exact mul_pos halpha h2
  · rw [if_neg h]
    exact h2

/-- THEOREM: the Euclideanized tuple at spacing `a` is the unit-spacing
tuple scaled by `a^2`. -/
theorem euclideanSqEdges_scale (ty : CausalPentType) (a alpha : ℝ) :
    euclideanSqEdges ty a alpha
      = fun e => a ^ 2 * euclideanSqEdges ty 1 alpha e := by
  funext e
  unfold euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-! ## §3. The Wick rotation as a map on squared edge lengths -/

/-- The Wick map: flip the sign of every timelike squared edge length,
leave spacelike squared edge lengths unchanged. -/
def wick (ty : CausalPentType) (x : SqEdges10) : SqEdges10 :=
  fun e => if isTimelike ty e then -(x e) else x e

/-- THEOREM: the Wick map is an involution on all of `SqEdges10` (hence in
particular on the causal class). -/
theorem wick_wick (ty : CausalPentType) (x : SqEdges10) :
    wick ty (wick ty x) = x := by
  funext e
  by_cases h : isTimelike ty e = true
  · simp only [wick, if_pos h, neg_neg]
  · simp only [wick, if_neg h]

/-- THEOREM: the Wick map is involutive (Mathlib `Function.Involutive`
packaging of `wick_wick`). -/
theorem wick_involutive (ty : CausalPentType) :
    Function.Involutive (wick ty) :=
  fun x => wick_wick ty x

/-- THEOREM: on the causal class the Wick map produces exactly the
Euclideanized tuple. -/
theorem wick_lorentzian (ty : CausalPentType) (a alpha : ℝ) :
    wick ty (lorentzianSqEdges ty a alpha) = euclideanSqEdges ty a alpha := by
  funext e
  by_cases h : isTimelike ty e = true
  · simp only [wick, lorentzianSqEdges, euclideanSqEdges, if_pos h, neg_neg]
  · simp only [wick, lorentzianSqEdges, euclideanSqEdges, if_neg h]

/-- THEOREM: the Euclideanized tuple is the honest algebraic continuation
`alpha ↦ -alpha` of the Lorentzian tuple. -/
theorem lorentzian_continuation (ty : CausalPentType) (a alpha : ℝ) :
    lorentzianSqEdges ty a (-alpha) = euclideanSqEdges ty a alpha := by
  funext e
  unfold lorentzianSqEdges euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]

/-- THEOREM: combining the two, the Wick map acts on the causal class as
the continuation `alpha ↦ -alpha`. -/
theorem wick_eq_continuation (ty : CausalPentType) (a alpha : ℝ) :
    wick ty (lorentzianSqEdges ty a alpha) = lorentzianSqEdges ty a (-alpha) :=
  (wick_lorentzian ty a alpha).trans (lorentzian_continuation ty a alpha).symm

/-- THEOREM: the Wick image of any member of the Lorentzian causal class is
an Euclideanized tuple for some admissible parameters (`0 < a`,
`0 < alpha`), namely the witnessing parameters of the class membership. -/
theorem wick_image_euclidean (ty : CausalPentType) (x : SqEdges10)
    (hx : x ∈ LorentzianClass ty) :
    ∃ a alpha : ℝ, 0 < a ∧ 0 < alpha
      ∧ wick ty x = euclideanSqEdges ty a alpha := by
  simp only [LorentzianClass, Set.mem_setOf_eq] at hx
  obtain ⟨a, alpha, ha, halpha, hxeq⟩ := hx
  exact ⟨a, alpha, ha, halpha, by rw [hxeq, wick_lorentzian]⟩

/-! ## §4. The 4-simplex Cayley-Menger determinant `cm4`

`cm4` is grounded in the existing dimension-parametric machinery
`Geometry.CayleyMengerN`: the edge tuple is packaged as
`SimplexSquaredDistances 4`, and `cm4 := -(cmDetN)` so that `cm4 > 0` on
non-degenerate Euclidean 4-simplices (`cm4 = 9216 V^2`, i.e.
`simplexVolumeSqN = cm4 / 9216`, proved below). -/

/-- Squared-distance table of the 4-simplex from the `Fin 10` edge tuple
(lexicographic edge order). -/
def pentDistSq (x : SqEdges10) : Fin 5 → Fin 5 → ℝ := fun i j =>
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

/-- THEOREM: the distance table returns the edge tuple on every edge (the
table and the lexicographic edge indexing agree). -/
theorem pentDistSq_edge (x : SqEdges10) (e : Fin 10) :
    pentDistSq x (pentEdgeVertices e).1 (pentEdgeVertices e).2 = x e := by
  fin_cases e <;> rfl

/-- The `SimplexSquaredDistances 4` package of an edge tuple. -/
def pentDistances (x : SqEdges10) : SimplexSquaredDistances 4 where
  distSq := pentDistSq x
  symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  diag_zero := by
    intro i
    fin_cases i <;> rfl

/-- The 4-simplex Cayley-Menger determinant, sign-normalized so that
`cm4 > 0` on non-degenerate Euclidean 4-simplices (`cm4 = 9216 V^2`). -/
def cm4 (x : SqEdges10) : ℝ :=
  -(cmDetN (pentDistances x))

/-- THEOREM: the formal squared 4-volume of the repo's n-dimensional layer
is exactly `cm4 / 9216` (`9216 = 2^4 * (4!)^2`), fixing the sign and
normalization of `cm4` against `Geometry.CayleyMengerN`. -/
theorem simplexVolumeSqN_eq_cm4_div (x : SqEdges10) :
    simplexVolumeSqN (pentDistances x) = cm4 x / 9216 := by
  unfold simplexVolumeSqN cm4
  have h : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by
    norm_num [Nat.factorial]
  rw [h]
  ring

/-! ### The two-parameter causal matrices

On a causal tuple all ten edges take one of two values (`p` spacelike,
`q` timelike), so the bordered 6x6 CM matrix collapses to an explicit
two-parameter matrix per type.  The determinant of each is computed
symbolically once, and every causal evaluation follows by substitution. -/

/-- The bordered CM matrix of a (4,1) tuple with spacelike value `p` and
timelike value `q` (matrix rows/cols `1..5` are vertices `0..4`; the apex
vertex 4 is row/col 5). -/
def pentMatrix41 (p q : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
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
    | 1, 5 => q
    | 5, 1 => q
    | 2, 5 => q
    | 5, 2 => q
    | 3, 5 => q
    | 5, 3 => q
    | 4, 5 => q
    | 5, 4 => q
    | _, _ => p

/-- The bordered CM matrix of a (3,2) tuple with spacelike value `p` and
timelike value `q` (rows/cols `1,2,3` are the lower-slice vertices `0,1,2`;
rows/cols `4,5` are the upper-slice vertices `3,4`). -/
def pentMatrix32 (p q : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
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
    | 1, 2 => p
    | 2, 1 => p
    | 1, 3 => p
    | 3, 1 => p
    | 2, 3 => p
    | 3, 2 => p
    | 4, 5 => p
    | 5, 4 => p
    | _, _ => q

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
/-- THEOREM (symbolic 6x6 determinant): the (4,1) causal CM determinant is
`p^3 * (3*p - 8*q)`.  Kernel-honest expansion of the bordered 6x6
determinant. -/
theorem det_pentMatrix41 (p q : ℝ) :
    Matrix.det (pentMatrix41 p q) = p ^ 3 * (3 * p - 8 * q) := by
  unfold pentMatrix41
  -- Style note: bare `simp` retained deliberately.  A `simp only` variant
  -- with an explicit lemma list was attempted and hit a deterministic
  -- whnf timeout even at 8M heartbeats (the default simp set's numeric
  -- simprocs are needed to keep the 6x6 expansion tractable).
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16384 in
/-- THEOREM (symbolic 6x6 determinant): the (3,2) causal CM determinant is
`p^3 * (7*p - 12*q)`. -/
theorem det_pentMatrix32 (p q : ℝ) :
    Matrix.det (pentMatrix32 p q) = p ^ 3 * (7 * p - 12 * q) := by
  unfold pentMatrix32
  -- Style note: bare `simp` retained deliberately; see det_pentMatrix41.
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- THEOREM: the bordered CM matrix of the Euclideanized (4,1) tuple is the
two-parameter matrix at `p = a^2`, `q = alpha * a^2`. -/
theorem cmMatrixN_euclidean_fourOne (a alpha : ℝ) :
    cmMatrixN (pentDistances (euclideanSqEdges CausalPentType.fourOne a alpha))
      = pentMatrix41 (a ^ 2) (alpha * a ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- THEOREM: the bordered CM matrix of the Lorentzian (4,1) tuple is the
two-parameter matrix at `p = a^2`, `q = -(alpha * a^2)`. -/
theorem cmMatrixN_lorentzian_fourOne (a alpha : ℝ) :
    cmMatrixN (pentDistances (lorentzianSqEdges CausalPentType.fourOne a alpha))
      = pentMatrix41 (a ^ 2) (-(alpha * a ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- THEOREM: the bordered CM matrix of the Euclideanized (3,2) tuple is the
two-parameter matrix at `p = a^2`, `q = alpha * a^2`. -/
theorem cmMatrixN_euclidean_threeTwo (a alpha : ℝ) :
    cmMatrixN (pentDistances (euclideanSqEdges CausalPentType.threeTwo a alpha))
      = pentMatrix32 (a ^ 2) (alpha * a ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- THEOREM: the bordered CM matrix of the Lorentzian (3,2) tuple is the
two-parameter matrix at `p = a^2`, `q = -(alpha * a^2)`. -/
theorem cmMatrixN_lorentzian_threeTwo (a alpha : ℝ) :
    cmMatrixN (pentDistances (lorentzianSqEdges CausalPentType.threeTwo a alpha))
      = pentMatrix32 (a ^ 2) (-(alpha * a ^ 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- THEOREM: type (4,1) Euclideanized Cayley-Menger determinant,
`cm4 = (8*alpha - 3) * a^8`.  Cross-check: the AJL volume
`V(4,1) = (a^4/96) * sqrt (8*alpha - 3)` gives
`9216 V^2 = (8*alpha - 3) * a^8`. -/
theorem cm4_euclidean_fourOne (a alpha : ℝ) :
    cm4 (euclideanSqEdges CausalPentType.fourOne a alpha)
      = (8 * alpha - 3) * a ^ 8 := by
  unfold cm4 cmDetN
  rw [cmMatrixN_euclidean_fourOne, det_pentMatrix41]
  ring

/-- THEOREM: type (3,2) Euclideanized Cayley-Menger determinant,
`cm4 = (12*alpha - 7) * a^8`.  Cross-check: the AJL volume
`V(3,2) = (a^4/96) * sqrt (12*alpha - 7)` gives
`9216 V^2 = (12*alpha - 7) * a^8`. -/
theorem cm4_euclidean_threeTwo (a alpha : ℝ) :
    cm4 (euclideanSqEdges CausalPentType.threeTwo a alpha)
      = (12 * alpha - 7) * a ^ 8 := by
  unfold cm4 cmDetN
  rw [cmMatrixN_euclidean_threeTwo, det_pentMatrix32]
  ring

/-- THEOREM: type (4,1) Lorentzian Cayley-Menger determinant,
`cm4 = -((8*alpha + 3) * a^8)`: strictly negative for `alpha ≥ 0`, `0 < a`
(see `lorentzian_cm4_neg_fourOne`). -/
theorem cm4_lorentzian_fourOne (a alpha : ℝ) :
    cm4 (lorentzianSqEdges CausalPentType.fourOne a alpha)
      = -((8 * alpha + 3) * a ^ 8) := by
  unfold cm4 cmDetN
  rw [cmMatrixN_lorentzian_fourOne, det_pentMatrix41]
  ring

/-- THEOREM: type (3,2) Lorentzian Cayley-Menger determinant,
`cm4 = -((12*alpha + 7) * a^8)`. -/
theorem cm4_lorentzian_threeTwo (a alpha : ℝ) :
    cm4 (lorentzianSqEdges CausalPentType.threeTwo a alpha)
      = -((12 * alpha + 7) * a ^ 8) := by
  unfold cm4 cmDetN
  rw [cmMatrixN_lorentzian_threeTwo, det_pentMatrix32]
  ring

/-- THEOREM: `a^2` scales out of the causal Cayley-Menger determinant with
weight `(a^2)^4 = a^8`, stated via the two exact evaluations.  The bordered
CM determinant of a 4-simplex is homogeneous of degree 4 in the squared
distances (the 4D analog of `cm3_scaling` with exponent 3 in 3D). -/
theorem cm4_euclidean_scale (ty : CausalPentType) (a alpha : ℝ) :
    cm4 (euclideanSqEdges ty a alpha)
      = (a ^ 2) ^ 4 * cm4 (euclideanSqEdges ty 1 alpha) := by
  cases ty
  · rw [cm4_euclidean_fourOne, cm4_euclidean_fourOne]
    ring
  · rw [cm4_euclidean_threeTwo, cm4_euclidean_threeTwo]
    ring

/-- THEOREM: at `alpha = 1`, `a = 1`, both causal types Euclideanize to the
regular unit 4-simplex tuple (all squared lengths 1). -/
theorem euclideanSqEdges_alpha_one (ty : CausalPentType) :
    euclideanSqEdges ty 1 1 = fun _ => (1 : ℝ) := by
  funext e
  unfold euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

/-- THEOREM (sanity anchor): the regular unit 4-simplex has `cm4 = 5`
(classical: `V = sqrt 5 / 96`, so `9216 V^2 = 5`). -/
theorem cm4_regular_unit : cm4 (fun _ => (1 : ℝ)) = 5 := by
  rw [← euclideanSqEdges_alpha_one CausalPentType.fourOne,
    cm4_euclidean_fourOne]
  norm_num

/-! ## §5. The exact non-degeneracy range (the core theorem) -/

/-- The exact non-degeneracy threshold for each causal type:
`alphaMin fourOne = 3/8`, `alphaMin threeTwo = 7/12`. -/
def alphaMin : CausalPentType → ℝ
  | CausalPentType.fourOne => 3 / 8
  | CausalPentType.threeTwo => 7 / 12

theorem alphaMin_fourOne : alphaMin CausalPentType.fourOne = 3 / 8 := rfl

theorem alphaMin_threeTwo : alphaMin CausalPentType.threeTwo = 7 / 12 := rfl

theorem alphaMin_pos (ty : CausalPentType) : 0 < alphaMin ty := by
  cases ty <;> norm_num [alphaMin]

theorem alphaMin_lt_one (ty : CausalPentType) : alphaMin ty < 1 := by
  cases ty <;> norm_num [alphaMin]

/-- THEOREM (core, exact range): for `0 < a`, the Euclideanized causal
4-simplex satisfies the CM positivity criterion `cm4 > 0` if and only if
`alpha > alphaMin ty`.  The threshold is exact in both directions.
Reading note: `cm4 > 0` is `9216 * simplexVolumeSqN > 0` (proved above);
its classical equivalence to embeddability in R^4 is not formalized in
this repo for n = 4 (3D analog: `Geometry/TetrahedronRealization.lean`). -/
theorem cm4_euclidean_pos_iff (ty : CausalPentType) (a alpha : ℝ)
    (ha : 0 < a) :
    0 < cm4 (euclideanSqEdges ty a alpha) ↔ alphaMin ty < alpha := by
  have h8 : 0 < a ^ 8 := pow_pos ha 8
  cases ty
  · rw [cm4_euclidean_fourOne, alphaMin_fourOne]
    constructor
    · intro h
      by_contra hle
      push_neg at hle
      have hprod : 0 ≤ (3 - 8 * alpha) * a ^ 8 :=
        mul_nonneg (by linarith) h8.le
      linarith
    · intro h
      have hprod : 0 < (8 * alpha - 3) * a ^ 8 :=
        mul_pos (by linarith) h8
      linarith
  · rw [cm4_euclidean_threeTwo, alphaMin_threeTwo]
    constructor
    · intro h
      by_contra hle
      push_neg at hle
      have hprod : 0 ≤ (7 - 12 * alpha) * a ^ 8 :=
        mul_nonneg (by linarith) h8.le
      linarith
    · intro h
      have hprod : 0 < (12 * alpha - 7) * a ^ 8 :=
        mul_pos (by linarith) h8
      linarith

/-- THEOREM: non-degeneracy on the derived range (forward direction of the
iff, stated for direct use). -/
theorem cm4_euclidean_pos (ty : CausalPentType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : alphaMin ty < alpha) :
    0 < cm4 (euclideanSqEdges ty a alpha) :=
  (cm4_euclidean_pos_iff ty a alpha ha).mpr halpha

/-- THEOREM: both causal types are simultaneously non-degenerate exactly on
`alpha > 7/12`, the standard 4d CDT Euclidean-regime bound. -/
theorem cm4_euclidean_pos_joint (a alpha : ℝ)
    (ha : 0 < a) (halpha : 7 / 12 < alpha) :
    0 < cm4 (euclideanSqEdges CausalPentType.fourOne a alpha)
      ∧ 0 < cm4 (euclideanSqEdges CausalPentType.threeTwo a alpha) :=
  ⟨cm4_euclidean_pos CausalPentType.fourOne a alpha ha
      (by rw [alphaMin_fourOne]; linarith),
    cm4_euclidean_pos CausalPentType.threeTwo a alpha ha
      (by rw [alphaMin_threeTwo]; linarith)⟩

/-- THEOREM (threshold exactness): at `alpha = alphaMin ty` the
Euclideanized 4-simplex is degenerate, `cm4 = 0`. -/
theorem cm4_euclidean_degenerate_at_min (ty : CausalPentType) (a : ℝ) :
    cm4 (euclideanSqEdges ty a (alphaMin ty)) = 0 := by
  cases ty
  · rw [alphaMin_fourOne, cm4_euclidean_fourOne]
    norm_num
  · rw [alphaMin_threeTwo, cm4_euclidean_threeTwo]
    norm_num

/-- THEOREM: the Lorentzian (4,1) tuple always fails the Cayley-Menger
positivity criterion: `cm4 < 0` for all `alpha ≥ 0`, `0 < a`.  What is
proved here is exactly this sign fact.  Upgrading it to "not
Euclidean-realizable" needs the classical Cayley-Menger realizability
theorem (`cm4 > 0` iff embeddable in R^4), which is not formalized in this
repo for n = 4 (3D analog: `Geometry/TetrahedronRealization.lean`).  Under
that classical reading the Wick rotation is genuinely required to reach the
Euclidean sector. -/
theorem lorentzian_cm4_neg_fourOne (a alpha : ℝ)
    (ha : 0 < a) (halpha : 0 ≤ alpha) :
    cm4 (lorentzianSqEdges CausalPentType.fourOne a alpha) < 0 := by
  rw [cm4_lorentzian_fourOne]
  have h8 : 0 < a ^ 8 := pow_pos ha 8
  have hprod : 0 < (8 * alpha + 3) * a ^ 8 := mul_pos (by linarith) h8
  linarith

/-- THEOREM: same for the Lorentzian (3,2) tuple. -/
theorem lorentzian_cm4_neg_threeTwo (a alpha : ℝ)
    (ha : 0 < a) (halpha : 0 ≤ alpha) :
    cm4 (lorentzianSqEdges CausalPentType.threeTwo a alpha) < 0 := by
  rw [cm4_lorentzian_threeTwo]
  have h8 : 0 < a ^ 8 := pow_pos ha 8
  have hprod : 0 < (12 * alpha + 7) * a ^ 8 := mul_pos (by linarith) h8
  linarith

/-! ## §6. `NonDegeneratePent` packaging and the certified Wick composite -/

/-- A non-degenerate Euclidean 4-simplex in the cm4 criterion: all squared
edges positive and `cm4 > 0` (the 4D analogue of the Regge foundation's
`NonDegenerateTet`). -/
structure NonDegeneratePent where
  sqEdge : SqEdges10
  sqEdge_pos : ∀ e, 0 < sqEdge e
  cm_pos : 0 < cm4 sqEdge

/-- def (packaged witness): on the exact range `alpha > alphaMin ty` (with
`0 < a`), the Euclideanized causal 4-simplex packages into a
`NonDegeneratePent`: all squared edges positive and `cm4 > 0`.  The
mathematical content lives in the two proof fields
(`euclideanSqEdges_pos`, `cm4_euclidean_pos`). -/
def euclideanCausalPent (ty : CausalPentType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : alphaMin ty < alpha) :
    NonDegeneratePent where
  sqEdge := euclideanSqEdges ty a alpha
  sqEdge_pos := fun e =>
    euclideanSqEdges_pos ty a alpha ha (lt_trans (alphaMin_pos ty) halpha) e
  cm_pos := cm4_euclidean_pos ty a alpha ha halpha

/-- THEOREM (composite): the Wick image of the Lorentzian causal tuple
satisfies `cm4 > 0` on the exact range.  This is the certified 4D
kinematical Wick rotation at the cm4-criterion level: Lorentzian class
member in, `cm4 > 0` out (non-degeneracy in the CM positivity sense; the
embeddability upgrade is classical and not formalized here). -/
theorem wick_lorentzian_nondegenerate (ty : CausalPentType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : alphaMin ty < alpha) :
    0 < cm4 (wick ty (lorentzianSqEdges ty a alpha)) := by
  rw [wick_lorentzian]
  exact cm4_euclidean_pos ty a alpha ha halpha

/-- def (packaged witness): the physical-point (`a = 1`, `alpha = 1`)
non-degenerate causal 4-simplex, for either type. -/
def physicalCausalPent (ty : CausalPentType) : NonDegeneratePent :=
  euclideanCausalPent ty 1 1 one_pos (alphaMin_lt_one ty)

/-! ## §7. Status certificate -/

/-- Status flags for the 4D Lorentzian lift.  This module certifies the 4D
kinematical layer: the causal 4-simplex classes are defined and
combinatorially verified, the exact cm4 thresholds `alpha > 3/8` (type
(4,1)) and `alpha > 7/12` (type (3,2)) are proved with degeneracy exactly
at threshold, and the Lorentzian tuples are proved to have `cm4 < 0`
(strict CM negativity; the embeddability upgrade to non-realizability is
classical and not formalized here).  The action-level continuation (complex
dihedral angles at timelike triangular hinges, the boost/sinh sector of the
4d Regge action) is wave 3b and remains OPEN, deliberately flagged below. -/
structure CausalSimplex4DStatus where
  four_d_classes_defined : Bool
  cm4_thresholds_certified : Bool
  lorentzian_cm4_negativity_proved : Bool
  action_level_continuation_open : Bool

/-- The status of this module's deliverables. -/
def causalSimplex4DStatus : CausalSimplex4DStatus where
  four_d_classes_defined := true
  cm4_thresholds_certified := true
  lorentzian_cm4_negativity_proved := true
  action_level_continuation_open := true

/-- Documentation record (by `rfl`): the flag values as set above.  The
mathematics lives in the theorems above, not in these booleans; nothing
forces hand-set flags.  Not counted in the THEOREM honesty tier. -/
theorem causalSimplex4DStatus_flags :
    causalSimplex4DStatus.four_d_classes_defined = true
      ∧ causalSimplex4DStatus.cm4_thresholds_certified = true
      ∧ causalSimplex4DStatus.lorentzian_cm4_negativity_proved = true
      ∧ causalSimplex4DStatus.action_level_continuation_open = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## §8. Axiom audit

`#print axioms` receipts for the four load-bearing determinant results.
Expected output for each: `[propext, Classical.choice, Quot.sound]`
(the standard Mathlib trio; no `sorryAx`, no `Lean.ofReduceBool` from
`native_decide`, no repo-local axioms).  The output appears as `info`
lines in the build log. -/

#print axioms det_pentMatrix41
#print axioms det_pentMatrix32
#print axioms cm4_euclidean_fourOne
#print axioms cm4_euclidean_threeTwo

end

end CausalSimplex4D
end SevenGaps
end Gravity
end IndisputableMonolith

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import IndisputableMonolith.Geometry.CayleyMengerPolynomial
import IndisputableMonolith.Geometry.ReggeRigorousFoundation
import IndisputableMonolith.Geometry.DihedralCayleyMenger

/-!
# Causal (CDT) Tetrahedron Classes and the Kinematical Wick Rotation (3D)

QG Seven-Gaps campaign, Lorentzian-sector lane.  Every prior result of the
discrete gravity program (formal and numerical) is Euclidean.  This module
builds the first certified Lorentzian layer:

1. the causal (CDT-style) tetrahedron classes in D = 3, with the
   spacelike/timelike edge-type assignment verified combinatorially from the
   slice structure (decide-able lemmas);
2. the Wick rotation as an explicit map on squared edge lengths, proved to be
   an involution and proved to act on the causal class as the algebraic
   continuation `alpha ↦ -alpha`;
3. a non-degeneracy theorem for the Euclideanized simplices on an exact,
   hand-derived parameter range, with `NonDegenerateTet` instances;
4. a deficit-angle reality corollary at the physical point `alpha = 1`.

## Conventions (3D CDT, Ambjorn-Jurkiewicz-Loll)

Spatial slices are 2D triangulated surfaces of equilateral triangles with
squared edge length `a^2`.  Spacetime between slices `t` and `t+1` is filled
by two tetrahedron types:

* type (3,1): three vertices on slice `t`, one on slice `t+1`
  (3 spacelike + 3 timelike edges); the time-reflected type (1,3) has the
  same edge-length multiset and is covered by the same theorems;
* type (2,2): two vertices on each slice (2 spacelike + 4 timelike edges).

Spacelike edges carry squared length `a^2`; timelike edges carry squared
length `-alpha * a^2` in the Lorentzian regime, `alpha > 0`.  The Wick
rotation flips the sign of the timelike squared lengths, i.e. it is the
continuation `alpha ↦ -alpha` on the causal class.

Vertex/edge indexing follows `Geometry.CayleyMengerPolynomial`: vertices
`0,1,2,3`, edges `0=(0,1), 1=(0,2), 2=(0,3), 3=(1,2), 4=(1,3), 5=(2,3)`.
Slice assignment: for (3,1) vertices `{0,1,2}` lie on slice `t` and `3` on
slice `t+1`; for (2,2) vertices `{0,1}` lie on slice `t` and `{2,3}` on
slice `t+1`.

## Derived thresholds (hand computation, certified below)

With the Cayley-Menger polynomial `cm3` (equal to `288 V^2` on realizable
tetrahedra) and the Euclideanized tuples:

* type (3,1): `cm3 = 2 * (3*alpha - 1) * a^6`, hence non-degenerate exactly
  for `alpha > 1/3` (`alphaMin threeOne = 1/3`); cross-check: the AJL volume
  `V(3,1) = (a^3/12) * sqrt (3*alpha - 1)` gives `288 V^2 = 2(3*alpha-1) a^6`;
* type (2,2): `cm3 = 4 * (2*alpha - 1) * a^6`, hence non-degenerate exactly
  for `alpha > 1/2` (`alphaMin twoTwo = 1/2`); cross-check:
  `V(2,2) = (a^3/12) * sqrt (4*alpha - 2)` gives `288 V^2 = 4(2*alpha-1) a^6`.

Both types are simultaneously non-degenerate exactly for `alpha > 1/2`, the
standard 3d CDT Euclidean-regime bound.  The degeneracy at the threshold is
also proved (`cm3 = 0` at `alpha = alphaMin`), so the range is exact.  On the
Lorentzian side `cm3 < 0` for all `alpha >= 0`, so the Lorentzian tuples are
never Euclidean-realizable and the Wick rotation is genuinely required.

## Honesty tiers

* THEOREM: every declared theorem in this file is proved with zero sorry,
  zero admit, zero new axioms; hypotheses are explicit (`0 < a`,
  `alphaMin ty < alpha`, etc.).
* MODEL: `CausalTetType`, `sliceOf`, `isTimelike`, `lorentzianSqEdges`,
  `euclideanSqEdges`, `wick`, `alphaMin` are definitional encodings of the
  standard 3d CDT conventions.
* OPEN: the action-level Lorentzian continuation (complex dihedral angles,
  the sinh-action sector, boost-angle assignments at timelike hinges) is not
  attempted here; see `LorentzianSectorStatus`.  The symbolic-alpha dihedral
  reality range (arccos arguments strictly inside `(-1,1)` for all
  `alpha > alphaMin`) is also left open: the cofactor denominators are square
  roots of degree-2 Cayley-Menger minors, and their symbolic sign control is
  a separate fight.  The deficit-angle reality corollary is therefore proved
  at the concrete physical point `alpha = 1` (both types), where the
  Euclideanized tuples coincide with the regular tetrahedron.

## decide usage (all on finite Bool-valued data, none on `ℝ`)

`isTimelike_threeOne_eq_crossSlice`, `isTimelike_twoTwo_eq_crossSlice`,
`slice_count_threeOne`, `slice_count_twoTwo`, `timelike_count_threeOne`,
`spacelike_count_threeOne`, `timelike_count_twoTwo`, `spacelike_count_twoTwo`.
No `native_decide` anywhere.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace CausalSimplexWick

open Geometry.CayleyMengerPolynomial
open Geometry.ReggeRigorousFoundation
open Geometry.DihedralCayleyMenger

/-! ## §1. The causal tetrahedron classes (combinatorial layer)

MODEL: the two 3d CDT tetrahedron types and their slice structure. -/

/-- The two causal tetrahedron types of 3d CDT between adjacent slices.
`threeOne` has three vertices on slice `t` and one on slice `t+1` (its time
reflection (1,3) has the same edge data); `twoTwo` has two vertices on each
slice. -/
inductive CausalTetType
  | threeOne
  | twoTwo

/-- Slice membership of each vertex (`false` = slice `t`, `true` = slice
`t+1`).  For (3,1): vertices `0,1,2` on slice `t`, vertex `3` on `t+1`.
For (2,2): vertices `0,1` on slice `t`, vertices `2,3` on `t+1`. -/
def sliceOf : CausalTetType → Fin 4 → Bool
  | CausalTetType.threeOne, v => v.val == 3
  | CausalTetType.twoTwo, v => (v.val == 2) || (v.val == 3)

/-- Edge-type assignment: `true` iff the edge is timelike (connects the two
slices).  For (3,1) the timelike edges are `{2,4,5}` (those touching the
apex vertex 3); for (2,2) they are `{1,2,3,4}` (the four cross edges). -/
def isTimelike : CausalTetType → Fin 6 → Bool
  | CausalTetType.threeOne, e => (e.val == 2) || (e.val == 4) || (e.val == 5)
  | CausalTetType.twoTwo, e =>
      (e.val == 1) || (e.val == 2) || (e.val == 3) || (e.val == 4)

/-- THEOREM (by `decide`): for type (3,1), an edge is timelike iff its two
endpoints (via the repo edge convention `edgeVertices`) lie on different
slices.  This verifies the edge-type table against the slice structure. -/
theorem isTimelike_threeOne_eq_crossSlice :
    ∀ e : Fin 6,
      isTimelike CausalTetType.threeOne e
        = (sliceOf CausalTetType.threeOne (edgeVertices e).1
            != sliceOf CausalTetType.threeOne (edgeVertices e).2) := by
  decide

/-- THEOREM (by `decide`): same cross-slice verification for type (2,2). -/
theorem isTimelike_twoTwo_eq_crossSlice :
    ∀ e : Fin 6,
      isTimelike CausalTetType.twoTwo e
        = (sliceOf CausalTetType.twoTwo (edgeVertices e).1
            != sliceOf CausalTetType.twoTwo (edgeVertices e).2) := by
  decide

/-- THEOREM (by `decide`): type (3,1) has 3 vertices on slice `t` and 1 on
slice `t+1`. -/
theorem slice_count_threeOne :
    (Finset.univ.filter fun v : Fin 4 =>
        sliceOf CausalTetType.threeOne v = false).card = 3
      ∧ (Finset.univ.filter fun v : Fin 4 =>
        sliceOf CausalTetType.threeOne v = true).card = 1 := by
  decide

/-- THEOREM (by `decide`): type (2,2) has 2 vertices on each slice. -/
theorem slice_count_twoTwo :
    (Finset.univ.filter fun v : Fin 4 =>
        sliceOf CausalTetType.twoTwo v = false).card = 2
      ∧ (Finset.univ.filter fun v : Fin 4 =>
        sliceOf CausalTetType.twoTwo v = true).card = 2 := by
  decide

/-- THEOREM (by `decide`): type (3,1) has exactly 3 timelike edges. -/
theorem timelike_count_threeOne :
    (Finset.univ.filter fun e : Fin 6 =>
      isTimelike CausalTetType.threeOne e = true).card = 3 := by
  decide

/-- THEOREM (by `decide`): type (3,1) has exactly 3 spacelike edges. -/
theorem spacelike_count_threeOne :
    (Finset.univ.filter fun e : Fin 6 =>
      isTimelike CausalTetType.threeOne e = false).card = 3 := by
  decide

/-- THEOREM (by `decide`): type (2,2) has exactly 4 timelike edges. -/
theorem timelike_count_twoTwo :
    (Finset.univ.filter fun e : Fin 6 =>
      isTimelike CausalTetType.twoTwo e = true).card = 4 := by
  decide

/-- THEOREM (by `decide`): type (2,2) has exactly 2 spacelike edges. -/
theorem spacelike_count_twoTwo :
    (Finset.univ.filter fun e : Fin 6 =>
      isTimelike CausalTetType.twoTwo e = false).card = 2 := by
  decide

noncomputable section

/-! ## §2. Lorentzian and Euclideanized squared-edge tuples

MODEL: the standard CDT edge-length assignments. -/

/-- Lorentzian squared-edge tuple: spacelike edges carry `a^2`, timelike
edges carry `-(alpha * a^2)`. -/
def lorentzianSqEdges (ty : CausalTetType) (a alpha : ℝ) : SqEdges :=
  fun e => if isTimelike ty e then -(alpha * a ^ 2) else a ^ 2

/-- Euclideanized squared-edge tuple: spacelike edges carry `a^2`, timelike
edges carry `+alpha * a^2` (the image of the Lorentzian tuple under the Wick
map, equivalently the continuation `alpha ↦ -alpha`). -/
def euclideanSqEdges (ty : CausalTetType) (a alpha : ℝ) : SqEdges :=
  fun e => if isTimelike ty e then alpha * a ^ 2 else a ^ 2

/-- The Lorentzian causal class: all Lorentzian tuples of the given type
with positive lattice spacing and positive asymmetry `alpha`. -/
def LorentzianClass (ty : CausalTetType) : Set SqEdges :=
  { x | ∃ a alpha : ℝ, 0 < a ∧ 0 < alpha ∧ x = lorentzianSqEdges ty a alpha }

/-- THEOREM: all entries of the Euclideanized tuple are positive when
`0 < a` and `0 < alpha`. -/
theorem euclideanSqEdges_pos (ty : CausalTetType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : 0 < alpha) (e : Fin 6) :
    0 < euclideanSqEdges ty a alpha e := by
  have h2 : 0 < a ^ 2 := pow_pos ha 2
  unfold euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h]
    exact mul_pos halpha h2
  · rw [if_neg h]
    exact h2

/-! ## §3. The Wick rotation as a map on squared edge lengths -/

/-- The Wick map: flip the sign of every timelike squared edge length,
leave spacelike squared edge lengths unchanged. -/
def wick (ty : CausalTetType) (x : SqEdges) : SqEdges :=
  fun e => if isTimelike ty e then -(x e) else x e

/-- THEOREM: the Wick map is an involution on all of `SqEdges` (hence in
particular on the causal class). -/
theorem wick_wick (ty : CausalTetType) (x : SqEdges) :
    wick ty (wick ty x) = x := by
  funext e
  by_cases h : isTimelike ty e = true
  · simp only [wick, if_pos h, neg_neg]
  · simp only [wick, if_neg h]

/-- THEOREM: the Wick map is involutive (Mathlib `Function.Involutive`
packaging of `wick_wick`). -/
theorem wick_involutive (ty : CausalTetType) :
    Function.Involutive (wick ty) :=
  fun x => wick_wick ty x

/-- THEOREM: on the causal class the Wick map produces exactly the
Euclideanized tuple. -/
theorem wick_lorentzian (ty : CausalTetType) (a alpha : ℝ) :
    wick ty (lorentzianSqEdges ty a alpha) = euclideanSqEdges ty a alpha := by
  funext e
  by_cases h : isTimelike ty e = true
  · simp only [wick, lorentzianSqEdges, euclideanSqEdges, if_pos h, neg_neg]
  · simp only [wick, lorentzianSqEdges, euclideanSqEdges, if_neg h]

/-- THEOREM: the Euclideanized tuple is the honest algebraic continuation
`alpha ↦ -alpha` of the Lorentzian tuple. -/
theorem lorentzian_continuation (ty : CausalTetType) (a alpha : ℝ) :
    lorentzianSqEdges ty a (-alpha) = euclideanSqEdges ty a alpha := by
  funext e
  unfold lorentzianSqEdges euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]

/-- THEOREM: combining the two, the Wick map acts on the causal class as
the continuation `alpha ↦ -alpha`. -/
theorem wick_eq_continuation (ty : CausalTetType) (a alpha : ℝ) :
    wick ty (lorentzianSqEdges ty a alpha) = lorentzianSqEdges ty a (-alpha) :=
  (wick_lorentzian ty a alpha).trans (lorentzian_continuation ty a alpha).symm

/-- THEOREM: the Wick image of any member of the Lorentzian causal class is
an Euclideanized tuple with the same parameters. -/
theorem wick_image_euclidean (ty : CausalTetType) (x : SqEdges)
    (hx : x ∈ LorentzianClass ty) :
    ∃ a alpha : ℝ, 0 < a ∧ 0 < alpha ∧ wick ty x = euclideanSqEdges ty a alpha := by
  simp only [LorentzianClass, Set.mem_setOf_eq] at hx
  obtain ⟨a, alpha, ha, halpha, hxeq⟩ := hx
  exact ⟨a, alpha, ha, halpha, by rw [hxeq, wick_lorentzian]⟩

/-! ## §4. Cayley-Menger determinants of the causal tuples

The core computation.  `cm3` is the explicit degree-3 Cayley-Menger
polynomial from `Geometry.CayleyMengerPolynomial` with `cm3 = 288 V^2` on
realizable tetrahedra.  The repo already provides the uniform scaling law
`cm3_scaling : cm3 (fun e => s * x e) = s^3 * cm3 x`; we restate it for the
causal tuples (`cm3_euclidean_scale`) and also compute at general `a`
directly, so no generality is lost. -/

/-- THEOREM: type (3,1) Euclideanized Cayley-Menger determinant,
`cm3 = 2 * (3*alpha - 1) * a^6`.  Hand derivation: base `{a0,a1,a3} = a^2`
(equilateral spacelike triangle), legs `{a2,a4,a5} = alpha * a^2`; the three
balanced terms each contribute `alpha*(1+alpha)*a^6`, the four monomial
terms contribute `(1 + 3*alpha^2)*a^6`, leaving `2*(3*alpha - 1)*a^6`. -/
theorem cm3_euclidean_threeOne (a alpha : ℝ) :
    cm3 (euclideanSqEdges CausalTetType.threeOne a alpha)
      = 2 * (3 * alpha - 1) * a ^ 6 := by
  have h0 : euclideanSqEdges CausalTetType.threeOne a alpha 0 = a ^ 2 := rfl
  have h1 : euclideanSqEdges CausalTetType.threeOne a alpha 1 = a ^ 2 := rfl
  have h2 : euclideanSqEdges CausalTetType.threeOne a alpha 2 = alpha * a ^ 2 := rfl
  have h3 : euclideanSqEdges CausalTetType.threeOne a alpha 3 = a ^ 2 := rfl
  have h4 : euclideanSqEdges CausalTetType.threeOne a alpha 4 = alpha * a ^ 2 := rfl
  have h5 : euclideanSqEdges CausalTetType.threeOne a alpha 5 = alpha * a ^ 2 := rfl
  unfold cm3
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- THEOREM: type (2,2) Euclideanized Cayley-Menger determinant,
`cm3 = 4 * (2*alpha - 1) * a^6`.  Hand derivation: spacelike pair
`{a0,a5} = a^2` (an opposite-edge pair), cross edges
`{a1,a2,a3,a4} = alpha * a^2`; the first balanced term contributes
`(4*alpha - 2)*a^6`, the other two balanced terms give `2*alpha^2*a^6` each
and cancel exactly against the four monomial terms. -/
theorem cm3_euclidean_twoTwo (a alpha : ℝ) :
    cm3 (euclideanSqEdges CausalTetType.twoTwo a alpha)
      = 4 * (2 * alpha - 1) * a ^ 6 := by
  have h0 : euclideanSqEdges CausalTetType.twoTwo a alpha 0 = a ^ 2 := rfl
  have h1 : euclideanSqEdges CausalTetType.twoTwo a alpha 1 = alpha * a ^ 2 := rfl
  have h2 : euclideanSqEdges CausalTetType.twoTwo a alpha 2 = alpha * a ^ 2 := rfl
  have h3 : euclideanSqEdges CausalTetType.twoTwo a alpha 3 = alpha * a ^ 2 := rfl
  have h4 : euclideanSqEdges CausalTetType.twoTwo a alpha 4 = alpha * a ^ 2 := rfl
  have h5 : euclideanSqEdges CausalTetType.twoTwo a alpha 5 = a ^ 2 := rfl
  unfold cm3
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- THEOREM: type (3,1) Lorentzian Cayley-Menger determinant,
`cm3 = -(2 * (3*alpha + 1) * a^6)`: strictly negative for `alpha ≥ 0`,
`a ≠ 0` (see `lorentzian_cm3_neg_threeOne`). -/
theorem cm3_lorentzian_threeOne (a alpha : ℝ) :
    cm3 (lorentzianSqEdges CausalTetType.threeOne a alpha)
      = -(2 * (3 * alpha + 1) * a ^ 6) := by
  have h0 : lorentzianSqEdges CausalTetType.threeOne a alpha 0 = a ^ 2 := rfl
  have h1 : lorentzianSqEdges CausalTetType.threeOne a alpha 1 = a ^ 2 := rfl
  have h2 : lorentzianSqEdges CausalTetType.threeOne a alpha 2
      = -(alpha * a ^ 2) := rfl
  have h3 : lorentzianSqEdges CausalTetType.threeOne a alpha 3 = a ^ 2 := rfl
  have h4 : lorentzianSqEdges CausalTetType.threeOne a alpha 4
      = -(alpha * a ^ 2) := rfl
  have h5 : lorentzianSqEdges CausalTetType.threeOne a alpha 5
      = -(alpha * a ^ 2) := rfl
  unfold cm3
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- THEOREM: type (2,2) Lorentzian Cayley-Menger determinant,
`cm3 = -(4 * (2*alpha + 1) * a^6)`. -/
theorem cm3_lorentzian_twoTwo (a alpha : ℝ) :
    cm3 (lorentzianSqEdges CausalTetType.twoTwo a alpha)
      = -(4 * (2 * alpha + 1) * a ^ 6) := by
  have h0 : lorentzianSqEdges CausalTetType.twoTwo a alpha 0 = a ^ 2 := rfl
  have h1 : lorentzianSqEdges CausalTetType.twoTwo a alpha 1
      = -(alpha * a ^ 2) := rfl
  have h2 : lorentzianSqEdges CausalTetType.twoTwo a alpha 2
      = -(alpha * a ^ 2) := rfl
  have h3 : lorentzianSqEdges CausalTetType.twoTwo a alpha 3
      = -(alpha * a ^ 2) := rfl
  have h4 : lorentzianSqEdges CausalTetType.twoTwo a alpha 4
      = -(alpha * a ^ 2) := rfl
  have h5 : lorentzianSqEdges CausalTetType.twoTwo a alpha 5 = a ^ 2 := rfl
  unfold cm3
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- THEOREM: the Euclideanized tuple at spacing `a` is the unit-spacing tuple
scaled by `a^2`. -/
theorem euclideanSqEdges_scale (ty : CausalTetType) (a alpha : ℝ) :
    euclideanSqEdges ty a alpha
      = fun e => a ^ 2 * euclideanSqEdges ty 1 alpha e := by
  funext e
  unfold euclideanSqEdges
  by_cases h : isTimelike ty e = true
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- THEOREM: `a^2` scales out of the causal Cayley-Menger determinant via
the repo scaling law `cm3_scaling` (which already existed; nothing new
needed). -/
theorem cm3_euclidean_scale (ty : CausalTetType) (a alpha : ℝ) :
    cm3 (euclideanSqEdges ty a alpha)
      = (a ^ 2) ^ 3 * cm3 (euclideanSqEdges ty 1 alpha) := by
  rw [euclideanSqEdges_scale ty a alpha]
  exact cm3_scaling (euclideanSqEdges ty 1 alpha) (a ^ 2)

/-! ## §5. The exact non-degeneracy range (the core theorem) -/

/-- The exact non-degeneracy threshold for each causal type:
`alphaMin threeOne = 1/3`, `alphaMin twoTwo = 1/2`. -/
def alphaMin : CausalTetType → ℝ
  | CausalTetType.threeOne => 1 / 3
  | CausalTetType.twoTwo => 1 / 2

theorem alphaMin_threeOne : alphaMin CausalTetType.threeOne = 1 / 3 := rfl

theorem alphaMin_twoTwo : alphaMin CausalTetType.twoTwo = 1 / 2 := rfl

theorem alphaMin_pos (ty : CausalTetType) : 0 < alphaMin ty := by
  cases ty <;> norm_num [alphaMin]

theorem alphaMin_lt_one (ty : CausalTetType) : alphaMin ty < 1 := by
  cases ty <;> norm_num [alphaMin]

/-- THEOREM (core, exact range): for `0 < a`, the Euclideanized causal
tetrahedron is non-degenerate (`cm3 > 0`, equivalently positive squared
volume) if and only if `alpha > alphaMin ty`.  The threshold is exact in
both directions. -/
theorem cm3_euclidean_pos_iff (ty : CausalTetType) (a alpha : ℝ)
    (ha : 0 < a) :
    0 < cm3 (euclideanSqEdges ty a alpha) ↔ alphaMin ty < alpha := by
  have h6 : 0 < a ^ 6 := pow_pos ha 6
  cases ty
  · rw [cm3_euclidean_threeOne, alphaMin_threeOne]
    constructor
    · intro h
      by_contra hle
      push_neg at hle
      have hprod : 0 ≤ (1 - 3 * alpha) * a ^ 6 :=
        mul_nonneg (by linarith) h6.le
      linarith
    · intro h
      have hprod : 0 < (3 * alpha - 1) * a ^ 6 :=
        mul_pos (by linarith) h6
      linarith
  · rw [cm3_euclidean_twoTwo, alphaMin_twoTwo]
    constructor
    · intro h
      by_contra hle
      push_neg at hle
      have hprod : 0 ≤ (1 - 2 * alpha) * a ^ 6 :=
        mul_nonneg (by linarith) h6.le
      linarith
    · intro h
      have hprod : 0 < (2 * alpha - 1) * a ^ 6 :=
        mul_pos (by linarith) h6
      linarith

/-- THEOREM: non-degeneracy on the derived range (forward direction of the
iff, stated for direct use). -/
theorem cm3_euclidean_pos (ty : CausalTetType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : alphaMin ty < alpha) :
    0 < cm3 (euclideanSqEdges ty a alpha) :=
  (cm3_euclidean_pos_iff ty a alpha ha).mpr halpha

/-- THEOREM: both causal types are simultaneously non-degenerate exactly on
`alpha > 1/2`, the standard 3d CDT Euclidean-regime bound. -/
theorem cm3_euclidean_pos_joint (a alpha : ℝ)
    (ha : 0 < a) (halpha : 1 / 2 < alpha) :
    0 < cm3 (euclideanSqEdges CausalTetType.threeOne a alpha)
      ∧ 0 < cm3 (euclideanSqEdges CausalTetType.twoTwo a alpha) :=
  ⟨cm3_euclidean_pos CausalTetType.threeOne a alpha ha
      (by rw [alphaMin_threeOne]; linarith),
    cm3_euclidean_pos CausalTetType.twoTwo a alpha ha
      (by rw [alphaMin_twoTwo]; linarith)⟩

/-- THEOREM (threshold exactness): at `alpha = alphaMin ty` the Euclideanized
simplex is degenerate, `cm3 = 0`. -/
theorem cm3_euclidean_degenerate_at_min (ty : CausalTetType) (a : ℝ) :
    cm3 (euclideanSqEdges ty a (alphaMin ty)) = 0 := by
  cases ty
  · rw [alphaMin_threeOne, cm3_euclidean_threeOne]
    norm_num
  · rw [alphaMin_twoTwo, cm3_euclidean_twoTwo]
    norm_num

/-- THEOREM: the Lorentzian (3,1) tuple always fails the Cayley-Menger
non-degeneracy criterion: `cm3 < 0` for all `alpha ≥ 0`, `0 < a`.  Formally
this is the cm3 sign fact; "not Euclidean-realizable" is the standard
reading via the classical Cayley-Menger realizability theorem (cm3 = 288 V²
on realizable tetrahedra), which is used as the interface convention of
`NonDegenerateTet`, not re-proved here.  The Wick rotation is genuinely
required to reach the Euclidean sector. -/
theorem lorentzian_cm3_neg_threeOne (a alpha : ℝ)
    (ha : 0 < a) (halpha : 0 ≤ alpha) :
    cm3 (lorentzianSqEdges CausalTetType.threeOne a alpha) < 0 := by
  rw [cm3_lorentzian_threeOne]
  have h6 : 0 < a ^ 6 := pow_pos ha 6
  have hprod : 0 < (3 * alpha + 1) * a ^ 6 := mul_pos (by linarith) h6
  linarith

/-- THEOREM: same for the Lorentzian (2,2) tuple. -/
theorem lorentzian_cm3_neg_twoTwo (a alpha : ℝ)
    (ha : 0 < a) (halpha : 0 ≤ alpha) :
    cm3 (lorentzianSqEdges CausalTetType.twoTwo a alpha) < 0 := by
  rw [cm3_lorentzian_twoTwo]
  have h6 : 0 < a ^ 6 := pow_pos ha 6
  have hprod : 0 < (2 * alpha + 1) * a ^ 6 := mul_pos (by linarith) h6
  linarith

/-! ## §6. `NonDegenerateTet` instances and the certified Wick composite -/

/-- THEOREM (packaged): on the exact range `alpha > alphaMin ty` (with
`0 < a`), the Euclideanized causal tetrahedron is a `NonDegenerateTet` of
the existing Regge foundation: all squared edges positive and `cm3 > 0`. -/
def euclideanCausalTet (ty : CausalTetType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : alphaMin ty < alpha) :
    NonDegenerateTet where
  sqEdge := euclideanSqEdges ty a alpha
  sqEdge_pos := fun e =>
    euclideanSqEdges_pos ty a alpha ha (lt_trans (alphaMin_pos ty) halpha) e
  cm_pos := cm3_euclidean_pos ty a alpha ha halpha

/-- THEOREM (composite): the Wick image of the Lorentzian causal tuple is
non-degenerate on the exact range.  This is the certified kinematical Wick
rotation: Lorentzian class member in, `NonDegenerateTet`-certified Euclidean
tetrahedron out (realizability in the cm3-criterion sense above). -/
theorem wick_lorentzian_nondegenerate (ty : CausalTetType) (a alpha : ℝ)
    (ha : 0 < a) (halpha : alphaMin ty < alpha) :
    0 < cm3 (wick ty (lorentzianSqEdges ty a alpha)) := by
  rw [wick_lorentzian]
  exact cm3_euclidean_pos ty a alpha ha halpha

/-- The physical-point (`a = 1`, `alpha = 1`) non-degenerate causal
tetrahedron, for either type. -/
def physicalCausalTet (ty : CausalTetType) : NonDegenerateTet :=
  euclideanCausalTet ty 1 1 one_pos (alphaMin_lt_one ty)

/-! ## §7. Deficit-angle reality corollary at the physical point

At `alpha = 1` (and unit spacing) both Euclideanized causal types coincide
with the regular unit tetrahedron, so the cofactor dihedral cosine is
exactly `1/3` at every edge and all dihedral angles are well-defined
(arccos arguments strictly inside `(-1,1)`), hence all deficit angles at
edges of the Euclideanized causal complex are real.  Downscope note (per
the lane ladder): the symbolic-alpha version of this corollary needs sign
control of the square-rooted degree-2 Cayley-Menger cofactor minors over the
whole range `alpha > alphaMin`; that fight is left OPEN and only the
concrete physical point is certified here.  The core non-degeneracy theorem
(§5) is symbolic in `alpha` for both types. -/

/-- THEOREM: at `alpha = 1`, `a = 1`, both causal types Euclideanize to the
regular unit tetrahedron tuple. -/
theorem euclideanSqEdges_alpha_one (ty : CausalTetType) :
    euclideanSqEdges ty 1 1 = regularUnitSqEdges := by
  funext e
  simp only [euclideanSqEdges, regularUnitSqEdges]
  by_cases h : isTimelike ty e = true
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

/-- THEOREM: at the physical point the cofactor dihedral cosine is `1/3` at
every edge (both causal types), via the proved regular-tetrahedron cofactor
evaluation. -/
theorem dihedralCos3Sq_alpha_one (ty : CausalTetType) (e : Fin 6) :
    dihedralCos3Sq (euclideanSqEdges ty 1 1) e = 1 / 3 := by
  rw [euclideanSqEdges_alpha_one ty]
  exact dihedralCos3_regularUnit e

/-- THEOREM (deficit-angle reality, physical point): the arccos argument
lies strictly inside `(-1, 1)` at every edge, for both causal types. -/
theorem dihedralCos3Sq_alpha_one_mem_Ioo (ty : CausalTetType) (e : Fin 6) :
    -1 < dihedralCos3Sq (euclideanSqEdges ty 1 1) e
      ∧ dihedralCos3Sq (euclideanSqEdges ty 1 1) e < 1 := by
  rw [dihedralCos3Sq_alpha_one ty e]
  norm_num

/-- THEOREM: the Euclidean dihedral angle at every edge of the physical-point
causal tetrahedron is `arccos (1/3)`, hence strictly inside `(0, π)`:
deficit angles at all edges are real and well-defined. -/
theorem dihedralAngle3_physical (ty : CausalTetType) (e : Fin 6) :
    dihedralAngle3 (physicalCausalTet ty) e = Real.arccos (1 / 3) :=
  congrArg Real.arccos (dihedralCos3Sq_alpha_one ty e)

/-- THEOREM: the physical-point dihedral angle lies strictly inside
`(0, π)`. -/
theorem dihedralAngle3_physical_mem_Ioo (ty : CausalTetType) (e : Fin 6) :
    0 < dihedralAngle3 (physicalCausalTet ty) e
      ∧ dihedralAngle3 (physicalCausalTet ty) e < Real.pi := by
  rw [dihedralAngle3_physical ty e]
  have h := Geometry.DihedralAngle.regular_tet_dihedral_in_open_interval
  rw [Geometry.DihedralAngle.regular_tet_dihedral_theta] at h
  exact h

/-! ## §8. Status certificate -/

/-- Status flags for the Lorentzian sector gap.  This module certifies the
kinematical Wick rotation on the causal class: the causal tetrahedron
classes are defined and combinatorially verified, the Wick map is a proved
involution acting as `alpha ↦ -alpha` on the class, and the Euclideanized
simplices are proved non-degenerate on the exact ranges `alpha > 1/3`
(type (3,1)) and `alpha > 1/2` (type (2,2)).  The action-level continuation
(complex dihedral angles at timelike hinges, the sinh/boost sector of the
Lorentzian Regge action, and the analytic continuation of the action itself)
remains OPEN and is deliberately flagged as such below. -/
structure LorentzianSectorStatus where
  causal_class_defined : Bool
  wick_certified_on_class : Bool
  euclidean_nondegeneracy_proved : Bool
  lorentzian_action_continuation_open : Bool

/-- The status of this module's deliverables. -/
def lorentzianSectorStatus : LorentzianSectorStatus where
  causal_class_defined := true
  wick_certified_on_class := true
  euclidean_nondegeneracy_proved := true
  lorentzian_action_continuation_open := true

/-- THEOREM (by `rfl`): the status flags are forced. -/
theorem lorentzianSectorStatus_flags :
    lorentzianSectorStatus.causal_class_defined = true
      ∧ lorentzianSectorStatus.wick_certified_on_class = true
      ∧ lorentzianSectorStatus.euclidean_nondegeneracy_proved = true
      ∧ lorentzianSectorStatus.lorentzian_action_continuation_open = true :=
  ⟨rfl, rfl, rfl, rfl⟩

end

end CausalSimplexWick
end SevenGaps
end Gravity
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Gravity.Analysis.ReggeHinge4DFlatKernel
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Regge 4D triangle-hinge orbit classification (Freudenthal / Kuhn cell)

QG full-theory campaign, combinatorial prerequisite for assembling the
flat Hessian from per-orbit star kernels.  Imports the 24 Kuhn
simplices / `vertexMask` API of `ReggeHinge4DFlatKernel` and the
15-class mask utilities of `ReggeEdgeStencil4D`; never redefines them.

## Tier tags (binding)

* THEOREM: every named theorem below (kernel-checked; no `sorry`, no
  `admit`, no new axioms, no `native_decide`, no `: True` shells).
* Scope: **combinatorics only** of triangle hinges in one unit 4-cube
  Kuhn triangulation, up to lattice translation (difference masks) and
  triangulation-preserving symmetry.
* This does **not** evaluate per-orbit star kernels (other than the
  already-committed seed orbit in `ReggeHinge4DStarKernel`).
* This does **not** complete the flat Hessian of the 4D Regge action.
* This does **not** prove `S_RS_converges_EH_4d`.
* This does **not** flip `gap_action_recovery`.

## What is proved (deliverable A, with honest refinement)

1. **Difference-mask type.** Every index-triple triangle in a Kuhn
   simplex is a monotone mask chain `m₀ ⊂ m₁ ⊂ m₂` with disjoint
   nonzero difference masks `(a,b) = (m₁⊕m₀, m₂⊕m₁)`; its type is the
   popcount pair `(|a|,|b|) ∈ {(1,1),(1,2),(2,1),(1,3),(3,1),(2,2)}`.
2. **Cell enumeration.** Exactly `24 · C(5,3) = 240` oriented
   triangle slots; per-type counts
   `(72,48,48,24,24,24)` for types
   `(1,1),(1,2),(2,1),(1,3),(3,1),(2,2)`.
3. **Lattice orbits under coordinate permutation.** Every realizable
   disjoint difference pair appears; the `S₄` action on bit positions
   preserves type and is transitive on realizable pairs of each type
   (six orbits).  The seed hinge `{0,e₀,e₀+e₁}` has type `(1,1)`.
4. **Complement symmetry.** Bitwise complement `m ↦ m ⊕ 15` sends
   Kuhn vertex-sets to Kuhn vertex-sets and swaps type `(i,j)` with
   `(j,i)`.  Under the larger triangulation-preserving group
   `S₄ ⋊ {id, complement}`, types `(1,2)~(2,1)` and `(1,3)~(3,1)`
   merge, yielding **four** lattice orbits.
5. **Within-cell absolute triangles.** Coordinate permutation does
   **not** act transitively on absolute mask-triples of a fixed type
   inside one cube (vertex-popcount profiles distinguish positions);
   lattice classification uses translation-normalized `(a,b)`, not
   absolute placement.
6. **Local squared-length package** for one representative of each of
   the six `S₄`-orbits (flat Hamming weights of edges `a`, `b`, `a∨b`).
7. **Gates:** seed nonvacuity; overlapping-mask decoy `(1,3)` is not
   a realizable difference pair.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace Analysis
namespace ReggeHinge4DOrbitClassification

open ReggeHinge4DFlatKernel
open ReggeEdgeStencil4D

/-! ## §1. Triangle slots and difference masks -/

/-- The `C(5,3) = 10` increasing vertex-index triples in a 4-simplex. -/
def triangleIndexTriple : Fin 10 → Fin 5 × Fin 5 × Fin 5
  | 0 => (0, 1, 2)
  | 1 => (0, 1, 3)
  | 2 => (0, 1, 4)
  | 3 => (0, 2, 3)
  | 4 => (0, 2, 4)
  | 5 => (0, 3, 4)
  | 6 => (1, 2, 3)
  | 7 => (1, 2, 4)
  | 8 => (1, 3, 4)
  | 9 => (2, 3, 4)
  | ⟨n + 10, h⟩ => absurd h (by omega)

/-- Hamming weight on the four low bits (masks in `{0,…,15}`). -/
def maskPop (m : ℕ) : ℕ :=
  (if Nat.testBit m 0 then 1 else 0) +
    (if Nat.testBit m 1 then 1 else 0) +
      (if Nat.testBit m 2 then 1 else 0) +
        (if Nat.testBit m 3 then 1 else 0)

/-- Ordered vertex masks of triangle slot `t` in simplex `s`. -/
def triangleVertexMasks (s : Fin 24) (t : Fin 10) : ℕ × ℕ × ℕ :=
  let p := triangleIndexTriple t
  (vertexMask s p.1, vertexMask s p.2.1, vertexMask s p.2.2)

/-- First difference mask `a = m₁ ⊕ m₀`. -/
def diffMaskA (s : Fin 24) (t : Fin 10) : ℕ :=
  let m := triangleVertexMasks s t
  Nat.xor m.2.1 m.1

/-- Second difference mask `b = m₂ ⊕ m₁`. -/
def diffMaskB (s : Fin 24) (t : Fin 10) : ℕ :=
  let m := triangleVertexMasks s t
  Nat.xor m.2.2 m.2.1

/-- Popcount-pair type of a triangle slot. -/
def hingeTypePop (s : Fin 24) (t : Fin 10) : ℕ × ℕ :=
  (maskPop (diffMaskA s t), maskPop (diffMaskB s t))

/-- The six lattice orbit types under coordinate permutation. -/
inductive HingeOrbitType
  | t11
  | t12
  | t21
  | t13
  | t31
  | t22
  deriving DecidableEq, Repr, Fintype

def HingeOrbitType.toPop : HingeOrbitType → ℕ × ℕ
  | .t11 => (1, 1)
  | .t12 => (1, 2)
  | .t21 => (2, 1)
  | .t13 => (1, 3)
  | .t31 => (3, 1)
  | .t22 => (2, 2)

def popToOrbitType : ℕ × ℕ → Option HingeOrbitType
  | (1, 1) => some .t11
  | (1, 2) => some .t12
  | (2, 1) => some .t21
  | (1, 3) => some .t13
  | (3, 1) => some .t31
  | (2, 2) => some .t22
  | _ => none

/-- THEOREM: every triangle slot has one of the six orbit types. -/
theorem hingeTypePop_is_orbitType (s : Fin 24) (t : Fin 10) :
    popToOrbitType (hingeTypePop s t) ≠ none := by
  fin_cases s <;> fin_cases t <;> decide

/-- Typed orbit of a triangle slot. -/
def hingeOrbitType (s : Fin 24) (t : Fin 10) : HingeOrbitType :=
  (popToOrbitType (hingeTypePop s t)).getD .t11

theorem hingeOrbitType_toPop (s : Fin 24) (t : Fin 10) :
    (hingeOrbitType s t).toPop = hingeTypePop s t := by
  fin_cases s <;> fin_cases t <;> decide

/-- THEOREM: difference masks of every triangle slot are nonzero,
pairwise bitwise disjoint, and OR-bounded by four bits. -/
theorem triangle_diff_masks_ok (s : Fin 24) (t : Fin 10) :
    0 < diffMaskA s t ∧ 0 < diffMaskB s t ∧
      Nat.land (diffMaskA s t) (diffMaskB s t) = 0 ∧
        diffMaskA s t ≤ 15 ∧ diffMaskB s t ≤ 15 := by
  fin_cases s <;> fin_cases t <;> decide

/-! ## §2. Per-type triangle counts in the 24-simplex cell -/

/-- Indicator that slot `(s,t)` has popcount type `p`. -/
def triangleTypeNat (s : Fin 24) (t : Fin 10) (p : ℕ × ℕ) : ℕ :=
  if hingeTypePop s t = p then 1 else 0

/-- Cell-wide count of oriented triangle slots of a given popcount type. -/
def cellTriangleCount (p : ℕ × ℕ) : ℕ :=
  ∑ s : Fin 24, ∑ t : Fin 10, triangleTypeNat s t p

theorem cellTriangleCount_t11 : cellTriangleCount (1, 1) = 72 := by
  decide

theorem cellTriangleCount_t12 : cellTriangleCount (1, 2) = 48 := by
  decide

theorem cellTriangleCount_t21 : cellTriangleCount (2, 1) = 48 := by
  decide

theorem cellTriangleCount_t13 : cellTriangleCount (1, 3) = 24 := by
  decide

theorem cellTriangleCount_t31 : cellTriangleCount (3, 1) = 24 := by
  decide

theorem cellTriangleCount_t22 : cellTriangleCount (2, 2) = 24 := by
  decide

/-- THEOREM: per-type oriented counts in one Kuhn cell. -/
theorem cellTriangleCount_values :
    cellTriangleCount (1, 1) = 72 ∧
      cellTriangleCount (1, 2) = 48 ∧
        cellTriangleCount (2, 1) = 48 ∧
          cellTriangleCount (1, 3) = 24 ∧
            cellTriangleCount (3, 1) = 24 ∧
              cellTriangleCount (2, 2) = 24 :=
  ⟨cellTriangleCount_t11, cellTriangleCount_t12, cellTriangleCount_t21,
    cellTriangleCount_t13, cellTriangleCount_t31, cellTriangleCount_t22⟩

/-- THEOREM: the six types partition all `240` oriented slots. -/
theorem cellTriangleCount_sum :
    cellTriangleCount (1, 1) + cellTriangleCount (1, 2) +
        cellTriangleCount (2, 1) + cellTriangleCount (1, 3) +
          cellTriangleCount (3, 1) + cellTriangleCount (2, 2) =
      240 := by
  simp [cellTriangleCount_t11, cellTriangleCount_t12, cellTriangleCount_t21,
    cellTriangleCount_t13, cellTriangleCount_t31, cellTriangleCount_t22]

theorem oriented_slot_total :
    (Fintype.card (Fin 24) * Fintype.card (Fin 10)) = 240 := by
  decide

/-! ## §3. Realizable difference pairs and decoy -/

/-- Whether `(a,b)` arises as the difference pair of some cell triangle. -/
def isRealizableDiffPair (a b : ℕ) : Bool :=
  decide (∃ s : Fin 24, ∃ t : Fin 10,
    diffMaskA s t = a ∧ diffMaskB s t = b)

/-- Bitwise-disjoint nonzero mask pair with masks in `{1,…,15}`. -/
def isDisjointDiffPair (a b : ℕ) : Bool :=
  decide (0 < a ∧ 0 < b ∧ a ≤ 15 ∧ b ≤ 15 ∧ Nat.land a b = 0)

/-- THEOREM: every disjoint nonzero 4-bit difference pair is realized. -/
theorem disjoint_implies_realizable (a b : Fin 15) :
    Nat.land (maskOf a) (maskOf b) = 0 →
      isRealizableDiffPair (maskOf a) (maskOf b) = true := by
  fin_cases a <;> fin_cases b <;> decide

/-- THEOREM (decoy): overlapping masks `(1,3)` are not a monotone
difference pair. -/
theorem decoy_overlapping_not_realizable :
    isRealizableDiffPair 1 3 = false := by
  decide

theorem decoy_overlapping_is_not_disjoint :
    isDisjointDiffPair 1 3 = false := by
  decide

/-- Seed hinge masks `{0,1,3}` as the slot `(s,t) = (0,0)`. -/
theorem seed_slot_masks :
    triangleVertexMasks 0 0 = (0, 1, 3) := by
  decide

/-- THEOREM (nonvacuity): the seed hinge has type `(1,1)`. -/
theorem seed_hinge_type_t11 :
    hingeTypePop 0 0 = (1, 1) ∧ hingeOrbitType 0 0 = .t11 := by
  decide

/-! ## §4. Coordinate-permutation action on masks -/

/-- Apply a coordinate permutation (as a `Fin 4 → Fin 4` map) to a mask. -/
def permMask (σ : Fin 4 → Fin 4) (m : ℕ) : ℕ :=
  (if Nat.testBit m 0 then 2 ^ (σ 0).val else 0) +
    (if Nat.testBit m 1 then 2 ^ (σ 1).val else 0) +
      (if Nat.testBit m 2 then 2 ^ (σ 2).val else 0) +
        (if Nat.testBit m 3 then 2 ^ (σ 3).val else 0)

/-- Lexicographic list of all 24 permutations of `Fin 4`, matching
`permAxes` order. -/
def coordPermOf (p : Fin 24) : Fin 4 → Fin 4 :=
  fun i =>
    match i, permAxes p with
    | 0, (a, _, _, _) => a
    | 1, (_, b, _, _) => b
    | 2, (_, _, c, _) => c
    | 3, (_, _, _, d) => d

def permDiffPair (σ : Fin 4 → Fin 4) (a b : ℕ) : ℕ × ℕ :=
  (permMask σ a, permMask σ b)

/-- THEOREM: every Kuhn coordinate permutation preserves `maskPop` on
4-bit masks. -/
theorem coordPerm_preserves_pop (p : Fin 24) (m : Fin 16) :
    maskPop (permMask (coordPermOf p) m.val) = maskPop m.val := by
  fin_cases p <;> fin_cases m <;> decide

/-- THEOREM: coordinate permutation preserves popcount type of a
difference pair. -/
theorem coordPerm_preserves_type (p : Fin 24) (a b : Fin 16) :
    (maskPop (permMask (coordPermOf p) a.val),
      maskPop (permMask (coordPermOf p) b.val)) =
      (maskPop a.val, maskPop b.val) := by
  simp [coordPerm_preserves_pop p a, coordPerm_preserves_pop p b]

/-- Canonical `S₄`-orbit representatives (one per popcount type). -/
def orbitRep : HingeOrbitType → ℕ × ℕ
  | .t11 => (1, 2)
  | .t12 => (1, 6)
  | .t21 => (3, 4)
  | .t13 => (1, 14)
  | .t31 => (7, 8)
  | .t22 => (3, 12)

theorem orbitRep_realizable (ty : HingeOrbitType) :
    isRealizableDiffPair (orbitRep ty).1 (orbitRep ty).2 = true := by
  cases ty <;> decide

theorem orbitRep_type (ty : HingeOrbitType) :
    (maskPop (orbitRep ty).1, maskPop (orbitRep ty).2) = ty.toPop := by
  cases ty <;> decide

/-- Whether `(a,b)` lies in the `S₄`-orbit of the canonical rep of `ty`. -/
def inOrbitOfRep (ty : HingeOrbitType) (a b : ℕ) : Bool :=
  decide (∃ p : Fin 24,
    permDiffPair (coordPermOf p) (orbitRep ty).1 (orbitRep ty).2 = (a, b))

/-- THEOREM: every realizable difference pair of a given type lies in
the single `S₄`-orbit of that type's representative (transitivity on
translation-normalized pairs). -/
theorem realizable_in_type_orbit (a b : Fin 15)
    (hdis : Nat.land (maskOf a) (maskOf b) = 0) :
    inOrbitOfRep
        (match popToOrbitType (maskPop (maskOf a), maskPop (maskOf b)) with
          | some ty => ty
          | none => .t11)
        (maskOf a) (maskOf b) =
      true := by
  fin_cases a <;> fin_cases b <;> first | decide | contradiction

/-- Cleaner packaging: realizable pairs match their type orbit. -/
theorem realizable_matches_rep_orbit (s : Fin 24) (t : Fin 10) :
    inOrbitOfRep (hingeOrbitType s t) (diffMaskA s t) (diffMaskB s t) =
      true := by
  fin_cases s <;> fin_cases t <;> decide

/-! ## §5. Complement symmetry merges `(i,j)` with `(j,i)` -/

/-- Bitwise complement inside the unit 4-cube. -/
def complementMask (m : ℕ) : ℕ := Nat.xor m 15

/-- THEOREM: complement sends every Kuhn simplex vertex-set to another
Kuhn simplex vertex-set in the same cell. -/
theorem complement_preserves_kuhn (s : Fin 24) :
    ∃ s' : Fin 24, ∀ i : Fin 5,
      vertexMask s' i = complementMask (vertexMask s (4 - i)) := by
  fin_cases s <;> decide

/-- Complement of a difference pair, after reversing the monotone chain:
`(a,b) ↦ (b,a)` on the nose when masks are complementary-nested. -/
theorem complement_swaps_diff_pair (s : Fin 24) (t : Fin 10) :
    ∃ s' : Fin 24, ∃ t' : Fin 10,
      diffMaskA s' t' = diffMaskB s t ∧
        diffMaskB s' t' = diffMaskA s t := by
  fin_cases s <;> fin_cases t <;> decide

/-- THEOREM: complement swaps popcount type `(i,j)` with `(j,i)`. -/
theorem complement_swaps_type (s : Fin 24) (t : Fin 10) :
    ∃ s' : Fin 24, ∃ t' : Fin 10,
      hingeTypePop s' t' =
        ((hingeTypePop s t).2, (hingeTypePop s t).1) := by
  fin_cases s <;> fin_cases t <;> decide

/-- The four orbits under `S₄` plus complement. -/
inductive HingeOrbitTypeModComplement
  | o11
  | o12
  | o13
  | o22
  deriving DecidableEq, Repr, Fintype

def HingeOrbitType.toModComplement : HingeOrbitType → HingeOrbitTypeModComplement
  | .t11 => .o11
  | .t12 | .t21 => .o12
  | .t13 | .t31 => .o13
  | .t22 => .o22

theorem orbit_count_S4 : Fintype.card HingeOrbitType = 6 := by
  decide

theorem orbit_count_S4_complement :
    Fintype.card HingeOrbitTypeModComplement = 4 := by
  decide

/-! ## §6. Absolute within-cell triangles: type is not an `S₄`-orbit -/

/-- Absolute vertex-mask triple of a slot, as a sorted 3-tuple of `ℕ`. -/
def absoluteTriple (s : Fin 24) (t : Fin 10) : ℕ × ℕ × ℕ :=
  triangleVertexMasks s t

/-- Apply a coordinate permutation to an absolute triple. -/
def permTriple (p : Fin 24) (tr : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (permMask (coordPermOf p) tr.1,
    permMask (coordPermOf p) tr.2.1,
    permMask (coordPermOf p) tr.2.2)

/-- THEOREM (honest refinement): coordinate permutation does **not**
act transitively on absolute `(1,1)` triangles in the cell.  The seed
`{0,1,3}` and the interior chain `{1,3,7}` have the same difference
type but lie in distinct absolute `S₄`-orbits. -/
theorem absolute_t11_not_S4_transitive :
    hingeTypePop 0 0 = (1, 1) ∧
      hingeTypePop 0 6 = (1, 1) ∧
        absoluteTriple 0 0 = (0, 1, 3) ∧
          absoluteTriple 0 6 = (1, 3, 7) ∧
            (∀ p : Fin 24, permTriple p (0, 1, 3) ≠ (1, 3, 7)) := by
  decide

/-! ## §7. Local squared-length data for star treatment -/

/-- Flat squared edge lengths of a hinge with difference masks `(a,b)`:
the three boundary edges have Hamming weights `|a|`, `|b|`, `|a∨b|`. -/
structure OrbitLocalSq where
  lenA : ℕ
  lenB : ℕ
  lenAB : ℕ
  deriving DecidableEq, Repr

def localSqOfDiff (a b : ℕ) : OrbitLocalSq :=
  ⟨maskPop a, maskPop b, maskPop (Nat.lor a b)⟩

def orbitLocalSq : HingeOrbitType → OrbitLocalSq
  | ty => localSqOfDiff (orbitRep ty).1 (orbitRep ty).2

theorem orbitLocalSq_values :
    orbitLocalSq .t11 = ⟨1, 1, 2⟩ ∧
      orbitLocalSq .t12 = ⟨1, 2, 3⟩ ∧
        orbitLocalSq .t21 = ⟨2, 1, 3⟩ ∧
          orbitLocalSq .t13 = ⟨1, 3, 4⟩ ∧
            orbitLocalSq .t31 = ⟨3, 1, 4⟩ ∧
              orbitLocalSq .t22 = ⟨2, 2, 4⟩ := by
  decide

/-- THEOREM: local squared lengths of a cell triangle match its
difference-mask Hamming data. -/
theorem slot_localSq (s : Fin 24) (t : Fin 10) :
    localSqOfDiff (diffMaskA s t) (diffMaskB s t) =
      orbitLocalSq (hingeOrbitType s t) := by
  fin_cases s <;> fin_cases t <;> decide

/-! ## §8. Status flags -/

def hinge4DOrbitClassificationStatus : List String :=
  [ "THEOREM: six S4 lattice orbits by popcount type; cell counts 72/48/48/24/24/24"
  , "THEOREM: S4+complement merges (1,2)~(2,1) and (1,3)~(3,1) to four orbits"
  , "THEOREM: absolute within-cell triangles of fixed type need not form one S4 orbit"
  , "OPEN: per-orbit star kernels for the five non-seed S4 orbits"
  , "OPEN: flat Hessian assembly over all hinge orbits"
  , "NONCLAIM: S_RS_converges_EH_4d / gap_action_recovery" ]

theorem hinge4DOrbitClassificationStatus_flags :
    hinge4DOrbitClassificationStatus.length = 6 ∧
      "OPEN: per-orbit star kernels for the five non-seed S4 orbits" ∈
        hinge4DOrbitClassificationStatus := by
  decide

end ReggeHinge4DOrbitClassification
end Analysis
end Gravity
end IndisputableMonolith

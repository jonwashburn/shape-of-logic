import Mathlib
import IndisputableMonolith.Gravity.SevenGaps.PathSumMeasure

/-!
# Full Theory Phase 0b: the simplicial subclass of the path-sum configuration class

## Status: THEOREM (0 sorry, 0 new axiom; `decide` is used only for finite
combinatorial checks on the explicit one-tetrahedron witness, no
`native_decide`).

`SevenGaps.PathSumMeasure.BoundedComplex B` is the garbage-inclusive
superclass of bounded incidence configurations: it contains every bounded
combinatorial triangulation but also non-simplicial configurations
(degenerate edges, repeated vertices in a tetrahedron, multi-edges, tets
whose 1-skeleton is missing from the edge list).  This module adds the
`IsSimplicial` predicate carving out the true simplicial subclass, proves
the predicate decidable, proves the subclass is a `Fintype` with strictly
positive cardinality (`simplicialComplex_card_pos`), and exhibits a
NON-EMPTY simplicial witness (the single tetrahedron with its full
1-skeleton, `oneTetComplex`) so positivity does not rest on the vacuous
empty complex alone.

The simplicial conditions:
1. no degenerate edges (distinct endpoints);
2. no multi-edges (edges are injective as unordered vertex pairs);
3. each tetrahedron has four distinct vertices;
4. skeleton closure: every vertex pair of every tetrahedron is realized by
   an edge of the complex.

These four conditions are the combinatorial content of "abstract simplicial
3-complex presented by its tetrahedra and 1-skeleton" for the incidence
shape carried by `BoundedComplex` (vertex/edge/tet lists).  Face (triangle)
data is not carried by `BoundedComplex`, so triangle closure is not
expressible here; this is honest scope, recorded in
`simplicialClassStatus`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace PathSumMeasure

/-! ## §1. The simplicial predicate -/

/-- Unordered-pair equality of ordered vertex pairs. -/
def sameUnorderedPair {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p = q ∨ p = q.swap

instance {n : ℕ} (p q : Fin n × Fin n) : Decidable (sameUnorderedPair p q) := by
  unfold sameUnorderedPair
  infer_instance

/-- **The simplicial predicate** on a bounded incidence configuration:
no degenerate edges, no multi-edges, injective tetrahedron corners, and
skeleton closure (every corner pair of every tet is an edge of the
complex). -/
def IsSimplicial {B : ℕ} (K : BoundedComplex B) : Prop :=
  (∀ e : Fin K.nE, (K.edgeVerts e).1 ≠ (K.edgeVerts e).2) ∧
  (∀ e e' : Fin K.nE,
    sameUnorderedPair (K.edgeVerts e) (K.edgeVerts e') → e = e') ∧
  (∀ t : Fin K.nT, Function.Injective (K.tetVerts t)) ∧
  (∀ (t : Fin K.nT) (i j : Fin 4), i ≠ j →
    ∃ e : Fin K.nE,
      sameUnorderedPair (K.edgeVerts e) (K.tetVerts t i, K.tetVerts t j))

/-- The simplicial predicate is decidable (all quantifiers range over
finite index types). -/
instance {B : ℕ} : DecidablePred (IsSimplicial (B := B)) := fun K => by
  unfold IsSimplicial
  infer_instance

/-! ## §2. Finiteness of the simplicial subclass -/

/-- The true simplicial subclass of the scoped path-sum configuration
class. -/
abbrev SimplicialComplex (B : ℕ) : Type :=
  {K : BoundedComplex B // IsSimplicial K}

/-- **THEOREM (finiteness of the simplicial subclass).**  The simplicial
subclass inherits finiteness from the proved finiteness of the superclass
(`instFintypeBoundedComplex`) and decidability of the predicate. -/
instance instFintypeSimplicialComplex (B : ℕ) : Fintype (SimplicialComplex B) :=
  Subtype.fintype _

/-- The empty complex is (vacuously) simplicial. -/
theorem emptyComplex_isSimplicial (B : ℕ) : IsSimplicial (emptyComplex B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e; exact e.elim0
  · intro e; exact e.elim0
  · intro t; exact t.elim0
  · intro t; exact t.elim0

instance (B : ℕ) : Nonempty (SimplicialComplex B) :=
  ⟨⟨emptyComplex B, emptyComplex_isSimplicial B⟩⟩

/-- **THEOREM (positive count).**  The simplicial subclass is nonempty for
every size cap, so the restricted path sum has a nontrivial configuration
space. -/
theorem simplicialComplex_card_pos (B : ℕ) :
    0 < Fintype.card (SimplicialComplex B) :=
  Fintype.card_pos

/-! ## §3. The non-vacuous witness: a single tetrahedron with full skeleton

Positivity via the empty complex alone would be a vacuity risk.  We
exhibit the smallest genuinely 3-dimensional simplicial complex: four
vertices, six edges (the complete 1-skeleton), one tetrahedron. -/

/-- Cap relaxation: a bounded complex at cap `B` is one at any cap
`B' ≥ B`, with identical incidence data. -/
def relax {B B' : ℕ} (h : B ≤ B') (K : BoundedComplex B) :
    BoundedComplex B' where
  nV := K.nV
  nE := K.nE
  nT := K.nT
  hV := le_trans K.hV h
  hE := le_trans K.hE h
  hT := le_trans K.hT h
  edgeVerts := K.edgeVerts
  tetVerts := K.tetVerts

/-- Cap relaxation preserves the simplicial predicate (the predicate reads
only the incidence data, which `relax` preserves definitionally). -/
theorem relax_isSimplicial {B B' : ℕ} (h : B ≤ B') {K : BoundedComplex B}
    (hK : IsSimplicial K) : IsSimplicial (relax h K) :=
  hK

/-- The six edges of the tetrahedron on four vertices, as ordered pairs
(i, j) with i < j. -/
def tetEdges : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The single-tetrahedron complex at the minimal cap: 4 vertices, 6 edges
(the complete 1-skeleton), 1 tetrahedron. -/
def oneTetComplex : BoundedComplex 6 where
  nV := 4
  nE := 6
  nT := 1
  hV := by omega
  hE := le_refl 6
  hT := by omega
  edgeVerts := tetEdges
  tetVerts := fun _ i => i

/-- **THEOREM (non-vacuous simplicial witness).**  The single-tetrahedron
complex is simplicial: distinct edge endpoints, no multi-edges, injective
corners, and every corner pair realized by one of the six skeleton edges.
Kernel-checked by `decide` on the finite index types (`Fin 4`, `Fin 6`,
`Fin 1`); no `native_decide`. -/
theorem oneTetComplex_isSimplicial : IsSimplicial oneTetComplex := by
  decide

/-- **THEOREM.**  Every cap `B ≥ 6` admits a genuinely 3-dimensional
simplicial configuration (one tetrahedron, full skeleton): the subclass
positivity is not carried by the empty complex alone. -/
theorem exists_simplicial_with_tet (B : ℕ) (hB : 6 ≤ B) :
    ∃ K : SimplicialComplex B, 0 < K.1.nT :=
  ⟨⟨relax hB oneTetComplex, relax_isSimplicial hB oneTetComplex_isSimplicial⟩,
    Nat.one_pos⟩

/-! ## §4. The restricted path sum -/

/-- The path sum restricted to the simplicial subclass, with the same
`1/|Aut|` measure and weight as `Z`. -/
noncomputable def Zsimp (B : ℕ) (w : BoundedComplex B → ℂ) : ℂ :=
  ∑ K : SimplicialComplex B, (mu K.1 : ℂ) * w K.1

/-- **THEOREM (UV-finiteness of the simplicial path sum).**  For unit-modulus
weights the restricted path sum is bounded by the simplicial configuration
count. -/
theorem Zsimp_norm_le_card (B : ℕ) (w : BoundedComplex B → ℂ)
    (hw : ∀ K, ‖w K‖ ≤ 1) :
    ‖Zsimp B w‖ ≤ (Fintype.card (SimplicialComplex B) : ℝ) := by
  unfold Zsimp
  calc ‖∑ K : SimplicialComplex B, (mu K.1 : ℂ) * w K.1‖
      ≤ ∑ K : SimplicialComplex B, ‖(mu K.1 : ℂ) * w K.1‖ := norm_sum_le _ _
    _ ≤ ∑ _K : SimplicialComplex B, (1 : ℝ) := by
        refine Finset.sum_le_sum fun K _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (mu_pos K.1)]
        calc mu K.1 * ‖w K.1‖
            ≤ 1 * 1 := mul_le_mul (mu_le_one K.1) (hw K.1)
              (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = (Fintype.card (SimplicialComplex B) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-! ## §5. Status ledger -/

/-- Status of the simplicial-subclass repair (Phase 0b).  Honest scope:
`BoundedComplex` carries no triangle (2-face) list, so triangle closure is
not expressible in this incidence shape; the four proved conditions are the
full simplicial content available at this shape. -/
structure SimplicialClassStatus where
  simplicial_predicate_decidable : Bool
  subclass_fintype_proved : Bool
  subclass_card_pos_proved : Bool
  nonvacuous_witness_constructed : Bool
  triangle_closure_expressible : Bool

/-- The Phase-0b status record. -/
def simplicialClassStatus : SimplicialClassStatus where
  simplicial_predicate_decidable := true
  subclass_fintype_proved := true
  subclass_card_pos_proved := true
  nonvacuous_witness_constructed := true
  triangle_closure_expressible := false

/-- Status flags (rfl-forced). -/
theorem simplicialClassStatus_flags :
    simplicialClassStatus.simplicial_predicate_decidable = true ∧
    simplicialClassStatus.subclass_fintype_proved = true ∧
    simplicialClassStatus.subclass_card_pos_proved = true ∧
    simplicialClassStatus.nonvacuous_witness_constructed = true ∧
    simplicialClassStatus.triangle_closure_expressible = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end PathSumMeasure
end SevenGaps
end Gravity
end IndisputableMonolith

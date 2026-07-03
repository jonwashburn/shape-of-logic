import Mathlib
import IndisputableMonolith.Cosmology.GradedRungCost

/-!
# Integer-rung descent preserves the unit-step invariant: the positive complement to Phase 58

Phase 56 (`GradedRungCost`) made the recognition-cost law depend on the forced
minimal-distinction invariant `UnitStep k E` (every adjacency changes the integer rung by at
most one). Phase 57 wired that law into the runtime cost meter. Phase 58
(`RecognitionUnitStepPreservation`) then proved the honest negative fact about the *real-valued*
mean move (`pairResolve`): a blind global "the dynamics preserves unit-step" claim is FALSE, and
the only correct statement is a local post-move criterion.

Phase 59 supplies the positive half on the object the cost meter actually charges: the integer
rung field `k : V -> Z`. The live engine does not move integer rungs by real means; it descends a
region by exactly one rung when a distinction is forced (T-3 descends one rung at a time). The
question Phase 56/57 leaves open is whether *that* update keeps `UnitStep` cycle to cycle. The
answer here is precise:

* `shiftDown_unitStep_of_cut`: descending an arbitrary set `S` by one rung preserves `UnitStep`
  exactly when every *cut* edge (one endpoint in `S`, one outside) stays within one rung after the
  move. Edges with both endpoints inside `S`, or both outside, are preserved for free (the gap is
  unchanged). This is the integer analogue of Phase 58's `pairResolve_unitStep_of_local`.
* `shiftDown_top_unitStep`: the cut condition is **discharged unconditionally** when `S` is the set
  of cells at the top rung `M` (any upper bound on the rungs present in `E`). A top-rung cell's
  neighbour is forced to sit exactly one rung below, so after the descent the cut gap is `0`. So
  descending the coarsest (top) rung, the natural parameter-free relaxation move, provably keeps
  the field unit-step, and the Phase-56 cost law applies to the next cycle.
* `exists_top_descent_unitStep`: for any nonempty edge set with a unit-step field, such a
  preserving descent exists with no externally supplied `M` (take `M` to be the realised maximum
  rung), and it is nontrivial (the top rung is attained).
* `shiftUp_bot_unitStep`: the dual, raising the bottom rung, by symmetry.
* `ckLevels_descend_min_breaks`: the necessity counterexample. On the three-site chain with rungs
  `0,1,2`, descending the *bottom* cell (rung `0`) sends it to `-1`, so its edge to the rung-`1`
  neighbour has gap `2` and `UnitStep` fails. Descending a non-top cell is therefore unsafe; the
  top-rung restriction in `shiftDown_top_unitStep` is necessary, not cosmetic.

HONEST STATUS: THEOREM, 0 `sorry`, no new axioms beyond Mathlib's standard three
(`propext`, `Classical.choice`, `Quot.sound`). This closes the "we need a Lean theorem that the
active dynamics preserves the `UnitStep` graded-rung invariant cycle to cycle" item with the exact
truth: the generic move does not (Phase 58), but the forced top-rung descent does (Phase 59), and
the cost meter is theorem-backed along that update.
-/

namespace IndisputableMonolith
namespace Cosmology
namespace RungDescentUnitStep

open GradedRungCost (UnitStep)

variable {V : Type*}

/-! ## §1. The one-rung descent of a set and its pointwise values -/

/-- Descend every cell in `S` by exactly one rung, leaving the rest fixed. This is the integer
single-rung move the T-3 refiner posts; it changes rungs by `1`, never by a real mean. -/
def shiftDown (S : V → Prop) [DecidablePred S] (k : V → ℤ) : V → ℤ :=
  fun v => if S v then k v - 1 else k v

/-- Raise every cell in `S` by exactly one rung (the dual move). -/
def shiftUp (S : V → Prop) [DecidablePred S] (k : V → ℤ) : V → ℤ :=
  fun v => if S v then k v + 1 else k v

lemma shiftDown_pos (S : V → Prop) [DecidablePred S] (k : V → ℤ) {v : V} (h : S v) :
    shiftDown S k v = k v - 1 := if_pos h

lemma shiftDown_neg (S : V → Prop) [DecidablePred S] (k : V → ℤ) {v : V} (h : ¬ S v) :
    shiftDown S k v = k v := if_neg h

lemma shiftUp_pos (S : V → Prop) [DecidablePred S] (k : V → ℤ) {v : V} (h : S v) :
    shiftUp S k v = k v + 1 := if_pos h

lemma shiftUp_neg (S : V → Prop) [DecidablePred S] (k : V → ℤ) {v : V} (h : ¬ S v) :
    shiftUp S k v = k v := if_neg h

/-! ## §2. The local cut criterion (integer analogue of Phase 58) -/

/-- **Local preservation criterion.** Descending a set `S` by one rung preserves `UnitStep` on the
whole edge set provided every *cut* edge (exactly one endpoint in `S`) remains within one rung
after the move. Edges with both endpoints in `S` keep their gap (both shift by `1`); edges with
neither endpoint in `S` are unchanged. So only the cut edges can break the invariant, and the
hypothesis controls exactly those. -/
theorem shiftDown_unitStep_of_cut (S : V → Prop) [DecidablePred S] (k : V → ℤ)
    (E : Finset (V × V)) (hunit : UnitStep k E)
    (hcut : ∀ p ∈ E, ((S p.1 ∧ ¬ S p.2) ∨ (¬ S p.1 ∧ S p.2)) →
        (shiftDown S k p.1 - shiftDown S k p.2 = 0
          ∨ shiftDown S k p.1 - shiftDown S k p.2 = 1
          ∨ shiftDown S k p.1 - shiftDown S k p.2 = -1)) :
    UnitStep (shiftDown S k) E := by
  intro p hp
  by_cases h1 : S p.1 <;> by_cases h2 : S p.2
  · -- both endpoints descend: the gap is unchanged
    rw [shiftDown_pos S k h1, shiftDown_pos S k h2]
    have hsame : (k p.1 - 1) - (k p.2 - 1) = k p.1 - k p.2 := by ring
    rw [hsame]; exact hunit p hp
  · -- cut edge: p.1 descends, p.2 stays
    exact hcut p hp (Or.inl ⟨h1, h2⟩)
  · -- cut edge: p.1 stays, p.2 descends
    exact hcut p hp (Or.inr ⟨h1, h2⟩)
  · -- neither endpoint descends: unchanged
    rw [shiftDown_neg S k h1, shiftDown_neg S k h2]; exact hunit p hp

/-! ## §3. Descending the top rung always preserves unit-step -/

/-- **Top-rung descent preserves `UnitStep` unconditionally.** If `M` bounds every rung present in
`E` and `S` is the set of cells at rung `M`, then descending `S` by one rung keeps the field
unit-step. The cut argument is forced: a top-rung cell's neighbour cannot be above it, and
`UnitStep` forbids it being two below, so the neighbour sits exactly one rung down; after the
descent the two endpoints meet at rung `M - 1` and the cut gap is `0`. -/
theorem shiftDown_top_unitStep (k : V → ℤ) (E : Finset (V × V)) (M : ℤ)
    (hunit : UnitStep k E) (hub : ∀ p ∈ E, k p.1 ≤ M ∧ k p.2 ≤ M) :
    UnitStep (shiftDown (fun v => k v = M) k) E := by
  apply shiftDown_unitStep_of_cut (fun v => k v = M) k E hunit
  intro p hp hcut
  obtain ⟨hub1, hub2⟩ := hub p hp
  have hstep := hunit p hp
  rcases hcut with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- k p.1 = M (in S), k p.2 ≠ M (out): neighbour is forced to M - 1
    have hb2 : k p.2 < M := lt_of_le_of_ne hub2 h2
    have hk2 : k p.2 = M - 1 := by omega
    have v1 : shiftDown (fun v => k v = M) k p.1 = k p.1 - 1 := shiftDown_pos _ k h1
    have v2 : shiftDown (fun v => k v = M) k p.2 = k p.2 := shiftDown_neg _ k h2
    left; rw [v1, v2]; omega
  · -- k p.1 ≠ M (out), k p.2 = M (in): symmetric
    have hb1 : k p.1 < M := lt_of_le_of_ne hub1 h1
    have hk1 : k p.1 = M - 1 := by omega
    have v1 : shiftDown (fun v => k v = M) k p.1 = k p.1 := shiftDown_neg _ k h1
    have v2 : shiftDown (fun v => k v = M) k p.2 = k p.2 - 1 := shiftDown_pos _ k h2
    left; rw [v1, v2]; omega

/-- The vertices that actually appear in an edge set. -/
def edgeVerts [DecidableEq V] (E : Finset (V × V)) : Finset V :=
  E.image Prod.fst ∪ E.image Prod.snd

lemma fst_mem_edgeVerts [DecidableEq V] {E : Finset (V × V)} {p : V × V} (hp : p ∈ E) :
    p.1 ∈ edgeVerts E :=
  Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

lemma snd_mem_edgeVerts [DecidableEq V] {E : Finset (V × V)} {p : V × V} (hp : p ∈ E) :
    p.2 ∈ edgeVerts E :=
  Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨p, hp, rfl⟩))

/-- **A preserving descent always exists.** For any nonempty edge set carrying a unit-step rung
field, take `M` to be the realised maximum rung; descending the top-rung cells preserves
`UnitStep`, and the descent is nontrivial because the maximum is attained. No external parameter
is supplied: `M` is read off the field. -/
theorem exists_top_descent_unitStep [DecidableEq V] (k : V → ℤ) (E : Finset (V × V))
    (hne : E.Nonempty) (hunit : UnitStep k E) :
    ∃ M : ℤ, (∃ v ∈ edgeVerts E, k v = M)
      ∧ UnitStep (shiftDown (fun v => k v = M) k) E := by
  have hVne : (edgeVerts E).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p.1, fst_mem_edgeVerts hp⟩
  have hImgNe : ((edgeVerts E).image k).Nonempty := hVne.image k
  set M : ℤ := ((edgeVerts E).image k).max' hImgNe with hM
  have hMmem : M ∈ (edgeVerts E).image k := Finset.max'_mem _ hImgNe
  obtain ⟨v, hv, hvk⟩ := Finset.mem_image.mp hMmem
  refine ⟨M, ⟨v, hv, hvk⟩, ?_⟩
  apply shiftDown_top_unitStep k E M hunit
  intro p hp
  refine ⟨?_, ?_⟩
  · exact Finset.le_max' _ (k p.1) (Finset.mem_image.mpr ⟨p.1, fst_mem_edgeVerts hp, rfl⟩)
  · exact Finset.le_max' _ (k p.2) (Finset.mem_image.mpr ⟨p.2, snd_mem_edgeVerts hp, rfl⟩)

/-! ## §4. The dual: raising the bottom rung -/

/-- **Bottom-rung raise preserves `UnitStep` unconditionally** (dual of `shiftDown_top_unitStep`).
If `m` bounds every rung from below and `S` is the set of cells at rung `m`, raising `S` by one
rung keeps the field unit-step: a bottom cell's neighbour is forced to be exactly one rung up, so
after the raise the cut gap is `0`. -/
theorem shiftUp_bot_unitStep (k : V → ℤ) (E : Finset (V × V)) (m : ℤ)
    (hunit : UnitStep k E) (hlb : ∀ p ∈ E, m ≤ k p.1 ∧ m ≤ k p.2) :
    UnitStep (shiftUp (fun v => k v = m) k) E := by
  intro p hp
  obtain ⟨hlb1, hlb2⟩ := hlb p hp
  have hstep := hunit p hp
  by_cases h1 : k p.1 = m <;> by_cases h2 : k p.2 = m
  · rw [shiftUp_pos _ k h1, shiftUp_pos _ k h2]
    have hsame : (k p.1 + 1) - (k p.2 + 1) = k p.1 - k p.2 := by ring
    rw [hsame]; exact hstep
  · -- k p.1 = m (raised), k p.2 ≠ m: neighbour forced to m + 1
    have hb2 : m < k p.2 := lt_of_le_of_ne hlb2 (Ne.symm h2)
    have hk2 : k p.2 = m + 1 := by omega
    rw [shiftUp_pos _ k h1, shiftUp_neg _ k h2]
    left; omega
  · -- k p.2 = m (raised), k p.1 ≠ m: symmetric
    have hb1 : m < k p.1 := lt_of_le_of_ne hlb1 (Ne.symm h1)
    have hk1 : k p.1 = m + 1 := by omega
    rw [shiftUp_neg _ k h1, shiftUp_pos _ k h2]
    left; omega
  · rw [shiftUp_neg _ k h1, shiftUp_neg _ k h2]; exact hstep

/-! ## §5. Necessity: descending a non-top cell breaks unit-step -/

/-- The three-site chain rung field `0, 1, 2` (the rung is the position index). -/
def ckLevels : Fin 3 → ℤ := fun i => (i.val : ℤ)

/-- The chain edges `0 -- 1 -- 2` (ordered, as the engine carries them). -/
def ckEdges : Finset (Fin 3 × Fin 3) :=
  {((0 : Fin 3), (1 : Fin 3)), ((1 : Fin 3), (2 : Fin 3))}

/-- The chain `0, 1, 2` is unit-step before any move. -/
theorem ckLevels_unitStep : UnitStep ckLevels ckEdges := by
  unfold UnitStep; decide

/-- **Necessity counterexample.** Descending the *bottom* cell (rung `0`) of the chain `0, 1, 2`
sends it to `-1`, so the edge to the rung-`1` neighbour has gap `2` and `UnitStep` fails. Only
descending the top rung is safe; the top-rung hypothesis of `shiftDown_top_unitStep` is necessary,
not cosmetic. -/
theorem ckLevels_descend_min_breaks :
    ¬ UnitStep (shiftDown (fun v => v = (0 : Fin 3)) ckLevels) ckEdges := by
  unfold UnitStep; decide

/-! ## §6. The bundled headline -/

/-- **Phase-59 headline.** On the integer rung field the cost meter charges, the forced top-rung
descent (the natural parameter-free relaxation move) preserves the unit-step invariant for any
unit-step field with a rung upper bound, so the Phase-56 cost law applies to the next cycle; and
the concrete chain `0, 1, 2` shows a non-top single-cell descent breaks it, so the restriction is
necessary. Together with Phase 58 (the real-valued mean move does not preserve unit-step globally)
this is the complete, honest answer to whether the dynamics preserves the graded-rung invariant. -/
theorem t59_rung_descent_preservation (k : V → ℤ) (E : Finset (V × V)) (M : ℤ)
    (hunit : UnitStep k E) (hub : ∀ p ∈ E, k p.1 ≤ M ∧ k p.2 ≤ M) :
    UnitStep (shiftDown (fun v => k v = M) k) E
    ∧ ¬ UnitStep (shiftDown (fun v => v = (0 : Fin 3)) ckLevels) ckEdges :=
  ⟨shiftDown_top_unitStep k E M hunit hub, ckLevels_descend_min_breaks⟩

end RungDescentUnitStep
end Cosmology
end IndisputableMonolith

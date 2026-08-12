import IndisputableMonolith.Geometry.PeriodicFreudenthalTorus4D
import IndisputableMonolith.Gravity.Analysis.ReggeEdgeStencil4D

/-!
# Gap 2 / 4D carrier track: period-doubling on the Freudenthal 4-torus

The 4D mirror of `Gap2FreudenthalPeriodDoubling` (3D), built on the typed
4D carrier of `Geometry/PeriodicFreudenthalTorus4D`. It supplies the
level-to-level maps the 4D `MetricRefinementFamily` will need at the typed
skeleton:

* the mod-`N` vertex projection `periodDoublingVertexMap4D` from the
  side-`(2*N)` 4-torus to the side-`N` 4-torus, intertwining the periodic
  bit-translations of the Kuhn skeleton;
* the class-copying edge projection `periodDoublingEdgeMap4D` (keeps the
  `Fin 15` displacement class), with endpoint commutation;
* simpliciality of the projection on Kuhn 4-simplices: the image of every
  fine Kuhn simplex is the coarse Kuhn simplex of the same index at the
  projected cell, with five distinct vertices when `1 < N`;
* the coarse-to-fine section `liftEdgeDoubled4D` and the section theorem
  `liftEdge4D_is_section`, proved by cases via four `reduceMod_of_lt`
  facts, mirroring the 3D proof structure;
* the bridge theorems verifying that the fifteen classes of this carrier
  are bit-for-bit the fifteen classes of `ReggeEdgeStencil4D`, and that the
  squared lengths agree (`dispWeight4` is `classWeightNat`).

Scope and honesty boundary (same discipline as the 3D module):
* THEOREM: every named result below, on the typed periodic skeleton.
  Class-copy is class-label bookkeeping on the skeleton, not a
  `MetricDecoration.sqEdge` pullback; Config-level coarsen, decoration
  pullback, and action step control are the next worker's 4D-instance job.
* This module does not touch `BoundedComplex` and does not assemble a
  `MetricRefinementFamily`.

Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2FreudenthalPeriodDoubling4D

open Geometry.PeriodicFreudenthalTorus4D
open Analysis.ReggeEdgeStencil4D

noncomputable section

/-! ## §1. Side-doubling vertex projection -/

instance instNeZero_two_mul (N : ℕ) [NeZero N] : NeZero (2 * N) :=
  ⟨Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) (NeZero.ne N)⟩

/-- Coordinatewise reduction `Fin (2*N) → Fin N`. -/
def reduceMod (N : ℕ) [NeZero N] (i : Fin (2 * N)) : Fin N :=
  ⟨i.val % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩

theorem reduceMod_val (N : ℕ) [NeZero N] (i : Fin (2 * N)) :
    (reduceMod N i).val = i.val % N :=
  rfl

/-- Reduction mod `N` intertwines the one-step periodic bit translation. -/
theorem reduceMod_addBit (N : ℕ) [NeZero N] (i : Fin (2 * N)) (b : Bool) :
    reduceMod N (addBit i b) = addBit (reduceMod N i) b := by
  ext
  change ((i.val + bit b) % (2 * N)) % N = (i.val % N + bit b) % N
  have hdiv : N ∣ 2 * N := ⟨2, by ring⟩
  have hmod2 : ((i.val + bit b) % (2 * N)) % N = (i.val + bit b) % N :=
    Nat.mod_mod_of_dvd _ hdiv
  have hsplit : (i.val + bit b) % N = (i.val % N + bit b) % N := by
    simp [Nat.add_mod]
  rw [hmod2, hsplit]

/-- Reduction below the modulus is the identity embedding. -/
theorem reduceMod_of_lt (N : ℕ) [NeZero N] (i : Fin (2 * N)) (hi : i.val < N) :
    reduceMod N i = ⟨i.val, hi⟩ := by
  ext
  exact Nat.mod_eq_of_lt hi

/-- The mod-`N` vertex projection from the side-`(2*N)` periodic 4-grid to
the side-`N` periodic 4-grid. -/
def periodDoublingVertexMap4D (N : ℕ) [NeZero N] :
    Vertex4 (2 * N) → Vertex4 N :=
  fun v =>
    (reduceMod N v.1, reduceMod N v.2.1, reduceMod N v.2.2.1,
      reduceMod N v.2.2.2)

/-- The vertex projection intertwines four-axis bit translations. -/
theorem periodDoublingVertexMap4D_addBits4 (N : ℕ) [NeZero N]
    (v : Vertex4 (2 * N)) (dx dy dz dw : Bool) :
    periodDoublingVertexMap4D N (addBits4 v dx dy dz dw) =
      addBits4 (periodDoublingVertexMap4D N v) dx dy dz dw := by
  simp [periodDoublingVertexMap4D, addBits4, reduceMod_addBit]

/-- The vertex projection intertwines the local 4-cube corner translations
used by every Kuhn 4-simplex. -/
theorem periodDoublingVertexMap4D_addVertexBits4 (N : ℕ) [NeZero N]
    (v : Vertex4 (2 * N)) (a : Fin 16) :
    periodDoublingVertexMap4D N (addVertexBits4 v a) =
      addVertexBits4 (periodDoublingVertexMap4D N v) a := by
  simp [addVertexBits4, periodDoublingVertexMap4D_addBits4]

/-- **Headline (vertex map).** The mod-`N` map is a well-defined map on
periodic 4-vertices intertwining the periodic identifications encoded by
`addBits4` and `addVertexBits4`. -/
theorem freudenthal4D_period_doubling_vertex_map (N : ℕ) [NeZero N]
    (v : Vertex4 (2 * N)) (dx dy dz dw : Bool) (a : Fin 16) :
    periodDoublingVertexMap4D N (addBits4 v dx dy dz dw) =
        addBits4 (periodDoublingVertexMap4D N v) dx dy dz dw ∧
      periodDoublingVertexMap4D N (addVertexBits4 v a) =
        addVertexBits4 (periodDoublingVertexMap4D N v) a :=
  ⟨periodDoublingVertexMap4D_addBits4 N v dx dy dz dw,
    periodDoublingVertexMap4D_addVertexBits4 N v a⟩

/-! ## §2. Edge projection and the class-copy property -/

/-- Edge projection: send the fine base vertex through the vertex map and
keep the positive displacement class. -/
def periodDoublingEdgeMap4D (N : ℕ) [NeZero N] :
    PeriodicEdge4 (2 * N) → PeriodicEdge4 N :=
  fun e => { base := periodDoublingVertexMap4D N e.base, disp := e.disp }

/-- Endpoints of a fine 4-edge project to the endpoints of its image. -/
theorem periodDoublingEdgeMap4D_endpoints (N : ℕ) [NeZero N]
    (e : PeriodicEdge4 (2 * N)) :
    (periodDoublingEdgeMap4D N e).endpoints =
      (periodDoublingVertexMap4D N e.endpoints.1,
        periodDoublingVertexMap4D N e.endpoints.2) := by
  cases e with
  | mk base disp =>
      let d := dispBits4 disp
      have h := periodDoublingVertexMap4D_addBits4 N base d.1 d.2.1 d.2.2.1 d.2.2.2
      simp only [periodDoublingEdgeMap4D, PeriodicEdge4.endpoints, d] at h ⊢
      exact Prod.ext rfl h.symm

/-- Squared displacement of the image equals that of the fine edge, because
the displacement class is preserved. -/
theorem periodDoublingEdgeMap4D_dispSq_eq (N : ℕ) [NeZero N]
    (e : PeriodicEdge4 (2 * N)) :
    periodicDispSqEdge4 (periodDoublingEdgeMap4D N e).disp =
      periodicDispSqEdge4 e.disp := by
  rfl

/-- **Headline (class copy).** The edge projection keeps the displacement
class, so the squared lattice displacement of the image is definitionally
equal to that of the fine edge, and the endpoints commute with the
projection. This is class-label bookkeeping on the typed skeleton (the
carrier-level analog of the 3D `decoration_pullback_class_copy`); the
Config-level decoration pullback is the 4D instance's job. -/
theorem freudenthal4D_period_doubling_edge_control (N : ℕ) [NeZero N]
    (e : PeriodicEdge4 (2 * N)) :
    periodicDispSqEdge4 (periodDoublingEdgeMap4D N e).disp ≤
      periodicDispSqEdge4 e.disp ∧
      (periodDoublingEdgeMap4D N e).endpoints =
        (periodDoublingVertexMap4D N e.endpoints.1,
          periodDoublingVertexMap4D N e.endpoints.2) :=
  ⟨le_of_eq (periodDoublingEdgeMap4D_dispSq_eq N e),
    periodDoublingEdgeMap4D_endpoints N e⟩

/-! ## §3. Simpliciality of the projection on Kuhn 4-simplices -/

/-- Vertex set of a periodic Kuhn 4-simplex. -/
def kuhnVertexSet {N : ℕ} [NeZero N] (cell : Vertex4 N) (σ : Fin 24) :
    Finset (Vertex4 N) :=
  Finset.univ.image fun k : Fin 5 => addVertexBits4 cell (kuhnVerts σ k)

theorem kuhnVertexSet_card (N : ℕ) [NeZero N] (hN : 1 < N)
    (cell : Vertex4 N) (σ : Fin 24) :
    (kuhnVertexSet cell σ).card = 5 := by
  unfold kuhnVertexSet
  have hf : Function.Injective (fun k : Fin 5 => addVertexBits4 cell (kuhnVerts σ k)) :=
    kuhn_corners_injective N hN cell σ
  rw [Finset.card_image_of_injective _ hf]
  simp

/-- **Headline (simplicial map).** The mod-`N` projection is simplicial on
the Kuhn skeleton: the image of every fine Kuhn 4-simplex is the coarse
Kuhn 4-simplex of the same local index at the projected cell, as an
equality of vertex sets. When `1 < N` the image has five distinct
vertices. -/
theorem freudenthal4D_period_doubling_simplicial_map (N : ℕ) [NeZero N]
    (hN : 1 < N) (cell : Vertex4 (2 * N)) (σ : Fin 24) :
    (kuhnVertexSet cell σ).image (periodDoublingVertexMap4D N) =
        kuhnVertexSet (periodDoublingVertexMap4D N cell) σ ∧
      (kuhnVertexSet (periodDoublingVertexMap4D N cell) σ).card = 5 := by
  constructor
  · ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨k, _, rfl⟩
      refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
      exact (periodDoublingVertexMap4D_addVertexBits4 N cell (kuhnVerts σ k)).symm
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨k, _, rfl⟩
      refine Finset.mem_image.mpr
        ⟨addVertexBits4 cell (kuhnVerts σ k), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
      · exact periodDoublingVertexMap4D_addVertexBits4 N cell (kuhnVerts σ k)
  · exact kuhnVertexSet_card N hN (periodDoublingVertexMap4D N cell) σ

/-- Explicit coarse 4-simplex witnessing simpliciality. Holds at every `N`;
nondegeneracy of the coarse simplex is `kuhnVertexSet_card` (`1 < N`). -/
theorem freudenthal4D_period_doubling_simplicial_witness (N : ℕ) [NeZero N]
    (cell : Vertex4 (2 * N)) (σ : Fin 24) :
    ∃ τ : PeriodicSimplex4 N,
      ∀ k : Fin 5,
        periodDoublingVertexMap4D N (addVertexBits4 cell (kuhnVerts σ k)) =
          addVertexBits4 τ.1 (kuhnVerts τ.2 k) :=
  ⟨(periodDoublingVertexMap4D N cell, σ), fun k =>
    periodDoublingVertexMap4D_addVertexBits4 N cell (kuhnVerts σ k)⟩

/-! ## §4. The coarse-to-fine section -/

/-- Embed a coarse coordinate into the doubled side by value. -/
def embedDouble (N : ℕ) [NeZero N] (i : Fin N) : Fin (2 * N) :=
  ⟨i.val, by
    have hi := i.isLt
    have hN : 0 < N := Nat.pos_of_neZero N
    omega⟩

/-- Canonical edge section: same displacement class, base embedded into the
doubled lattice by value. -/
def liftEdgeDoubled4D (N : ℕ) [NeZero N] (e : PeriodicEdge4 N) :
    PeriodicEdge4 (2 * N) where
  base :=
    (embedDouble N e.base.1, embedDouble N e.base.2.1,
      embedDouble N e.base.2.2.1, embedDouble N e.base.2.2.2)
  disp := e.disp

theorem liftEdgeDoubled4D_disp (N : ℕ) [NeZero N] (e : PeriodicEdge4 N) :
    (liftEdgeDoubled4D N e).disp = e.disp := rfl

/-- **MAJOR headline (section).** `liftEdgeDoubled4D` is a section of the
period-doubling edge projection: project the lift, recover the edge. Proved
by cases through four `reduceMod_of_lt` facts, mirroring the 3D
`liftEdge_is_section`. -/
theorem liftEdge4D_is_section (N : ℕ) [NeZero N] (e : PeriodicEdge4 N) :
    periodDoublingEdgeMap4D N (liftEdgeDoubled4D N e) = e := by
  cases e with
  | mk base disp =>
    cases base with
    | mk x yzw =>
      cases yzw with
      | mk y zw =>
        cases zw with
        | mk z w =>
          have hx : x.val < N := x.isLt
          have hy : y.val < N := y.isLt
          have hz : z.val < N := z.isLt
          have hw : w.val < N := w.isLt
          have hx2 : x.val < 2 * N := by
            have := Nat.pos_of_neZero N; omega
          have hy2 : y.val < 2 * N := by
            have := Nat.pos_of_neZero N; omega
          have hz2 : z.val < 2 * N := by
            have := Nat.pos_of_neZero N; omega
          have hw2 : w.val < 2 * N := by
            have := Nat.pos_of_neZero N; omega
          simp only [liftEdgeDoubled4D, periodDoublingEdgeMap4D,
            periodDoublingVertexMap4D, embedDouble]
          refine congrArg (fun b => PeriodicEdge4.mk b disp) ?_
          refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
          · exact reduceMod_of_lt N ⟨x.val, hx2⟩ hx
          · exact reduceMod_of_lt N ⟨y.val, hy2⟩ hy
          · exact reduceMod_of_lt N ⟨z.val, hz2⟩ hz
          · exact reduceMod_of_lt N ⟨w.val, hw2⟩ hw

/-- The section is injective (distinct coarse edges lift to distinct fine
edges). -/
theorem liftEdgeDoubled4D_injective (N : ℕ) [NeZero N] :
    Function.Injective (liftEdgeDoubled4D N) := by
  intro a b h
  have ha := liftEdge4D_is_section N a
  have hb := liftEdge4D_is_section N b
  rw [h] at ha
  exact ha.symm.trans hb

/-- **Class copy through the section.** The round trip through the
projection keeps the displacement class exactly; the squared lattice
displacement agrees on the nose. -/
theorem periodDoubling4D_class_copy (N : ℕ) [NeZero N] (e : PeriodicEdge4 N) :
    (periodDoublingEdgeMap4D N (liftEdgeDoubled4D N e)).disp = e.disp ∧
      periodicDispSqEdge4
          (periodDoublingEdgeMap4D N (liftEdgeDoubled4D N e)).disp =
        periodicDispSqEdge4 e.disp := by
  rw [liftEdge4D_is_section]
  exact ⟨rfl, rfl⟩

/-! ## §5. Bridge to the Regge 4D stencil (the count verification) -/

/-- **Bridge (class enumeration verified).** The fifteen displacement
classes of this carrier are bit-for-bit the fifteen classes of
`ReggeEdgeStencil4D`: coordinate `i` of class `d` is bit `i` of the mask
`d.val + 1` on both sides. -/
theorem dispBits4_eq_classBit (d : Fin 15) :
    dispBits4 d =
      (classBit d 0, classBit d 1, classBit d 2, classBit d 3) := by
  fin_cases d <;> decide

/-- The Hamming weights agree class-by-class with the stencil. -/
theorem dispWeight4_eq_classWeightNat (d : Fin 15) :
    dispWeight4 d = classWeightNat d := by
  fin_cases d <;> decide

/-- The carrier's squared class lengths are the stencil's squared class
lengths (`classDispSq`), hence sit on the recognition ladder by
`Gap1ClassLengths.classLength_in_recognition_ladder` (proved in
`Gap1ClassLengthsFromRecognitionCost`). -/
theorem periodicDispSqEdge4_eq_classDispSq (d : Fin 15) :
    periodicDispSqEdge4 d = classDispSq d := by
  rw [classDispSq_eq_weight]
  unfold periodicDispSqEdge4
  exact_mod_cast dispWeight4_eq_classWeightNat d

/-! ## §6. Package (real Props from the headline theorems) -/

/-- The headline facts assembled as a single Prop, under the side-length
hypothesis `1 < N` required for non-collapse of simplex images. Each
conjunct other than the side-length hypothesis is proved by a named theorem
of this module. -/
def freudenthal4D_period_doubling_package (N : ℕ) [NeZero N] : Prop :=
  1 < N ∧
    (∀ (v : Vertex4 (2 * N)) (dx dy dz dw : Bool) (a : Fin 16),
        periodDoublingVertexMap4D N (addBits4 v dx dy dz dw) =
            addBits4 (periodDoublingVertexMap4D N v) dx dy dz dw ∧
          periodDoublingVertexMap4D N (addVertexBits4 v a) =
            addVertexBits4 (periodDoublingVertexMap4D N v) a) ∧
      (∀ (cell : Vertex4 (2 * N)) (σ : Fin 24),
        (kuhnVertexSet cell σ).image (periodDoublingVertexMap4D N) =
            kuhnVertexSet (periodDoublingVertexMap4D N cell) σ ∧
          (kuhnVertexSet (periodDoublingVertexMap4D N cell) σ).card = 5) ∧
      (∀ e : PeriodicEdge4 (2 * N),
        periodicDispSqEdge4 (periodDoublingEdgeMap4D N e).disp ≤
            periodicDispSqEdge4 e.disp ∧
          (periodDoublingEdgeMap4D N e).endpoints =
            (periodDoublingVertexMap4D N e.endpoints.1,
              periodDoublingVertexMap4D N e.endpoints.2))

theorem freudenthal4D_period_doubling_package_holds (N : ℕ) [NeZero N]
    (hN : 1 < N) : freudenthal4D_period_doubling_package N :=
  ⟨hN,
    fun v dx dy dz dw a => freudenthal4D_period_doubling_vertex_map N v dx dy dz dw a,
    fun cell σ => freudenthal4D_period_doubling_simplicial_map N hN cell σ,
    fun e => freudenthal4D_period_doubling_edge_control N e⟩

#print axioms liftEdge4D_is_section
#print axioms freudenthal4D_period_doubling_edge_control
#print axioms freudenthal4D_period_doubling_simplicial_map
#print axioms freudenthal4D_period_doubling_vertex_map
#print axioms periodDoubling4D_class_copy
#print axioms dispBits4_eq_classBit
#print axioms periodicDispSqEdge4_eq_classDispSq
#print axioms freudenthal4D_period_doubling_package_holds

end

end Gap2FreudenthalPeriodDoubling4D
end SevenGaps
end Gravity
end IndisputableMonolith

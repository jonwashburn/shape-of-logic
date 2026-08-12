import IndisputableMonolith.Geometry.PeriodicFreudenthalTorus

/-!
# Gap 2 / Track A2.1: period-doubling projection on the Freudenthal torus

Critical-path construction toward the missing `coarsen` field of
`MetricRefinementFamily` (`MetricRefinementCarrierBlocker`). No level-to-level
map between triangulations existed in the library; this module supplies the
first one at the level of the typed periodic skeleton (vertices, typed edges,
tetrahedron vertex sets): the mod-`N` vertex projection from the side-`(2*N)`
canonical periodic Freudenthal torus to the side-`N` torus. It is not a
morphism of `canonicalPeriodicTriangulation` or of `BoundedComplex`, and it is
not a map on decorated configurations: `coarsen` in the family structure maps
`Config (n+1)` to `Config n`. This module discharges the typed-skeleton
projection. The Config-level pullback along a section of
`periodDoublingEdgeMap`, together with decoration pullback and geometric step
control, is assembled for the canonical schedule `side = 3·2ⁿ` in
`Gap2MetricRefinementFamilyInstance` (`liftEdge_is_section`,
`decoration_pullback_sqEdge`, pullback-based `action_step_control`). Continuum
limit and the 4D carrier remain OPEN.

What is proved (exactly):
* the coordinatewise mod-`N` map on `Vertex (2*N)` is well-defined and
  intertwines the periodic bit-translations of the Freudenthal cube skeleton;
* the image of every fine Freudenthal tetrahedron is a coarse Freudenthal
  tetrahedron (same local tet index, at the projected cell), as a set of
  vertices, with four distinct image vertices when `1 < N`;
* the edge projection copies the displacement class, so
  `periodicDispSqEdge` of the image is definitionally equal to that of the
  fine edge, and the endpoints commute with the projection. This is
  class-label bookkeeping on the typed skeleton, not `MetricDecoration.sqEdge`
  control; metric decoration pullback is proved on the canonical schedule in
  `Gap2MetricRefinementFamilyInstance.decoration_pullback_sqEdge`.

The carrier here is three-dimensional: the seven positive cube displacements of
`PeriodicFreudenthalTorus`. The fifteen classes of `Gap1Counting4DObstruction`
are the four-dimensional stencil and are not the edges of this torus. No 4D
typed periodic Freudenthal triangulation exists in the library
(`CanonicalFreudenthalTorus4D` is an index wrapper, not a triangulation), so
the first family instance is scoped to 3D; a 4D instance needs the 4D carrier
built first and these headlines replayed on it.

Why `1 < N` suffices (the fold question): a Freudenthal tetrahedron lives in
one unit cube, so two of its vertices identify under mod-`N` only if `N`
divides a unit offset, i.e. only at `N = 1`. Under `1 < N` every image
tetrahedron has four distinct vertices; the seam case projects adjacent cell
vertices `N-1` and `N` to `N-1` and `0`, which are distinct.

Honesty boundary:
* THEOREM: the three headline maps and their supporting lemmas, on the typed
  periodic skeleton.
* Assembled elsewhere (canonical schedule only): Config-level coarsen as the
  section pullback of `periodDoublingEdgeMap`, decoration pullback, mesh
  schedule, summable geometric step error, nondegeneracy, and the
  `MetricRefinementFamily` instance live in
  `Gap2MetricRefinementFamilyInstance`. Scope is the side-`3·2ⁿ` 3D torus;
  this module does not restate those theorems.
* OPEN: continuum limit (A2.2) and the 4D carrier.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2FreudenthalPeriodDoubling

open Geometry.PeriodicFreudenthalTorus
open Geometry.FreudenthalCubeTriangulation

noncomputable section

/-! ## §1. Side-doubling vertex projection -/

instance instNeZero_two_mul (N : ℕ) [NeZero N] : NeZero (2 * N) :=
  ⟨Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) (NeZero.ne N)⟩

/-- Coordinatewise reduction `Fin (2*N) → Fin N`. -/
def reduceMod (N : ℕ) [NeZero N] (i : Fin (2 * N)) : Fin N :=
  ⟨i.val % N, Nat.mod_lt _ (Nat.pos_of_neZero N)⟩

/-- The mod-`N` vertex projection from the side-`(2*N)` periodic lattice to the
side-`N` periodic lattice. -/
def periodDoublingVertexMap (N : ℕ) [NeZero N] :
    Vertex (2 * N) (2 * N) (2 * N) → Vertex N N N :=
  fun v => (reduceMod N v.1, reduceMod N v.2.1, reduceMod N v.2.2)

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

/-- The vertex projection intertwines three-axis bit translations. -/
theorem periodDoublingVertexMap_addBits (N : ℕ) [NeZero N]
    (v : Vertex (2 * N) (2 * N) (2 * N)) (dx dy dz : Bool) :
    periodDoublingVertexMap N (addBits v dx dy dz) =
      addBits (periodDoublingVertexMap N v) dx dy dz := by
  simp [periodDoublingVertexMap, addBits, reduceMod_addBit]

/-- The vertex projection intertwines the local cube-vertex translations used
by every Freudenthal tetrahedron. -/
theorem periodDoublingVertexMap_addVertexBits (N : ℕ) [NeZero N]
    (v : Vertex (2 * N) (2 * N) (2 * N)) (a : Fin 8) :
    periodDoublingVertexMap N (addVertexBits v a) =
      addVertexBits (periodDoublingVertexMap N v) a := by
  simp [addVertexBits, periodDoublingVertexMap_addBits]

/-- **Headline.** The mod-`N` map is a well-defined map on periodic vertices:
it sends `Vertex (2*N)` to `Vertex N` and intertwines the periodic
identifications encoded by `addBit` / `addBits` / `addVertexBits`. -/
theorem freudenthal_period_doubling_vertex_map (N : ℕ) [NeZero N]
    (v : Vertex (2 * N) (2 * N) (2 * N)) (dx dy dz : Bool) (a : Fin 8) :
    periodDoublingVertexMap N (addBits v dx dy dz) =
        addBits (periodDoublingVertexMap N v) dx dy dz ∧
      periodDoublingVertexMap N (addVertexBits v a) =
        addVertexBits (periodDoublingVertexMap N v) a :=
  ⟨periodDoublingVertexMap_addBits N v dx dy dz,
    periodDoublingVertexMap_addVertexBits N v a⟩

/-! ## §2. Simpliciality of the projection -/

/-- If two one-step bit translations of the same coordinate agree, the bits
agree when `1 < N`. -/
private theorem addBit_cancel (N : ℕ) [NeZero N] (hN : 1 < N)
    (c : Fin N) (b₁ b₂ : Bool) (h : addBit c b₁ = addBit c b₂) : b₁ = b₂ := by
  have hval : (c.val + bit b₁) % N = (c.val + bit b₂) % N := by
    simpa [addBit] using congrArg Fin.val h
  have h' : (c.val % N + bit b₁) % N = (c.val % N + bit b₂) % N := by
    simpa [Nat.add_mod] using hval
  -- `c.val < N`, so `c.val % N = c.val`.
  have hc : c.val % N = c.val := Nat.mod_eq_of_lt c.isLt
  rw [hc] at h'
  cases b₁ <;> cases b₂ <;> simp [bit] at h' ⊢
  · have hcases : c.val + 1 < N ∨ c.val + 1 = N := by omega
    cases hcases with
    | inl hlt =>
        have : (c.val + 1) % N = c.val + 1 := Nat.mod_eq_of_lt hlt
        omega
    | inr heq =>
        have : (c.val + 1) % N = 0 := by rw [heq, Nat.mod_self]
        omega
  · have hcases : c.val + 1 < N ∨ c.val + 1 = N := by omega
    cases hcases with
    | inl hlt =>
        have : (c.val + 1) % N = c.val + 1 := Nat.mod_eq_of_lt hlt
        omega
    | inr heq =>
        have : (c.val + 1) % N = 0 := by rw [heq, Nat.mod_self]
        omega

private theorem addBits_cancel_offsets (N : ℕ) [NeZero N] (hN : 1 < N)
    (cell : Vertex N N N) (dx₁ dy₁ dz₁ dx₂ dy₂ dz₂ : Bool)
    (h : addBits cell dx₁ dy₁ dz₁ = addBits cell dx₂ dy₂ dz₂) :
    dx₁ = dx₂ ∧ dy₁ = dy₂ ∧ dz₁ = dz₂ := by
  have hx : addBit cell.1 dx₁ = addBit cell.1 dx₂ := congrArg Prod.fst h
  have hy : addBit cell.2.1 dy₁ = addBit cell.2.1 dy₂ :=
    congrArg (fun v : Vertex N N N => v.2.1) h
  have hz : addBit cell.2.2 dz₁ = addBit cell.2.2 dz₂ :=
    congrArg (fun v : Vertex N N N => v.2.2) h
  exact ⟨addBit_cancel N hN cell.1 dx₁ dx₂ hx,
    addBit_cancel N hN cell.2.1 dy₁ dy₂ hy,
    addBit_cancel N hN cell.2.2 dz₁ dz₂ hz⟩

/-- On a side-`N` torus with `1 < N`, the four vertices of any Freudenthal
tetrahedron are pairwise distinct. -/
theorem freudenthal_tet_vertices_injective (N : ℕ) [NeZero N] (hN : 1 < N)
    (cell : Vertex N N N) (tet : Fin 6) :
    Function.Injective
      (fun k : Fin 4 => addVertexBits cell (tetVerts tet k)) := by
  intro a b h
  -- Equality of translated vertices forces equality of local bit offsets.
  have hcancel :
      vertexBits (tetVerts tet a) = vertexBits (tetVerts tet b) := by
    rcases addBits_cancel_offsets N hN cell
        (vertexBits (tetVerts tet a)).1
        (vertexBits (tetVerts tet a)).2.1
        (vertexBits (tetVerts tet a)).2.2
        (vertexBits (tetVerts tet b)).1
        (vertexBits (tetVerts tet b)).2.1
        (vertexBits (tetVerts tet b)).2.2
        (by simpa [addVertexBits] using h) with ⟨hx, hy, hz⟩
    apply Prod.ext
    · exact hx
    · apply Prod.ext <;> assumption
  -- Distinct local labels in each Freudenthal tet have distinct bit triples.
  fin_cases tet <;> fin_cases a <;> fin_cases b <;>
    simp [tetVerts, vertexBits] at hcancel ⊢

/-- Vertex set of a periodic Freudenthal tetrahedron. -/
def tetVertexSet {Nx Ny Nz : ℕ} [NeZero Nx] [NeZero Ny] [NeZero Nz]
    (cell : Vertex Nx Ny Nz) (tet : Fin 6) : Finset (Vertex Nx Ny Nz) :=
  Finset.univ.image fun k : Fin 4 => addVertexBits cell (tetVerts tet k)

theorem tetVertexSet_card (N : ℕ) [NeZero N] (hN : 1 < N)
    (cell : Vertex N N N) (tet : Fin 6) :
    (tetVertexSet cell tet).card = 4 := by
  unfold tetVertexSet
  rw [Finset.card_image_of_injective _ (freudenthal_tet_vertices_injective N hN cell tet)]
  simp

/-- **Headline.** The mod-`N` projection is simplicial: the image of every
fine Freudenthal tetrahedron is a coarse Freudenthal tetrahedron (same local
tet index, at the projected cell), as an equality of vertex sets. When
`1 < N` the image has four distinct vertices. -/
theorem freudenthal_period_doubling_simplicial_map (N : ℕ) [NeZero N]
    (hN : 1 < N) (cell : Vertex (2 * N) (2 * N) (2 * N)) (tet : Fin 6) :
    (tetVertexSet cell tet).image (periodDoublingVertexMap N) =
        tetVertexSet (periodDoublingVertexMap N cell) tet ∧
      (tetVertexSet (periodDoublingVertexMap N cell) tet).card = 4 := by
  constructor
  · ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨k, _, rfl⟩
      refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
      exact (periodDoublingVertexMap_addVertexBits N cell (tetVerts tet k)).symm
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨k, _, rfl⟩
      refine Finset.mem_image.mpr
        ⟨addVertexBits cell (tetVerts tet k), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
      · exact periodDoublingVertexMap_addVertexBits N cell (tetVerts tet k)
  · exact tetVertexSet_card N hN (periodDoublingVertexMap N cell) tet

/-- Explicit coarse tetrahedron witnessing simpliciality. Holds at every `N`,
including `N = 1`; nondegeneracy of the coarse tetrahedron is *not* claimed
here (that is `tetVertexSet_card`, which requires `1 < N`). -/
theorem freudenthal_period_doubling_simplicial_witness (N : ℕ) [NeZero N]
    (cell : Vertex (2 * N) (2 * N) (2 * N)) (tet : Fin 6) :
    ∃ τ : PeriodicTet N N N,
      ∀ k : Fin 4,
        periodDoublingVertexMap N (addVertexBits cell (tetVerts tet k)) =
          addVertexBits τ.1 (tetVerts τ.2 k) :=
  ⟨(periodDoublingVertexMap N cell, tet), fun k =>
    periodDoublingVertexMap_addVertexBits N cell (tetVerts tet k)⟩

/-! ## §3. Squared-edge control -/

/-- Edge projection: send the fine base vertex through the vertex map and keep
the positive displacement class. -/
def periodDoublingEdgeMap (N : ℕ) [NeZero N] :
    PeriodicEdge (2 * N) (2 * N) (2 * N) → PeriodicEdge N N N :=
  fun e => { base := periodDoublingVertexMap N e.base, disp := e.disp }

/-- Endpoints of a fine edge project to the endpoints of its image edge. -/
theorem periodDoublingEdgeMap_endpoints (N : ℕ) [NeZero N]
    (e : PeriodicEdge (2 * N) (2 * N) (2 * N)) :
    (periodDoublingEdgeMap N e).endpoints =
      (periodDoublingVertexMap N e.endpoints.1,
        periodDoublingVertexMap N e.endpoints.2) := by
  cases e with
  | mk base disp =>
      let d := dispBits disp
      have h := periodDoublingVertexMap_addBits N base d.1 d.2.1 d.2.2
      simp only [periodDoublingEdgeMap, PeriodicEdge.endpoints, d] at h ⊢
      exact Prod.ext rfl h.symm

/-- Squared displacement of the image equals that of the fine edge, because
the displacement class is preserved. -/
theorem periodDoublingEdgeMap_dispSq_eq (N : ℕ) [NeZero N]
    (e : PeriodicEdge (2 * N) (2 * N) (2 * N)) :
    periodicDispSqEdge (periodDoublingEdgeMap N e).disp =
      periodicDispSqEdge e.disp := by
  rfl

/-- **Headline.** Class-copied edge control: the edge projection keeps the
displacement class, so the squared lattice displacement of the image is
definitionally equal to that of the fine edge (hence is bounded above by it),
and the endpoints commute with the projection. This is a statement about
`periodicDispSqEdge` on the typed skeleton; it is not a
`MetricDecoration.sqEdge` pullback and does not by itself feed
`action_step_control`. -/
theorem freudenthal_period_doubling_edge_control (N : ℕ) [NeZero N]
    (e : PeriodicEdge (2 * N) (2 * N) (2 * N)) :
    periodicDispSqEdge (periodDoublingEdgeMap N e).disp ≤
      periodicDispSqEdge e.disp ∧
      (periodDoublingEdgeMap N e).endpoints =
        (periodDoublingVertexMap N e.endpoints.1,
          periodDoublingVertexMap N e.endpoints.2) :=
  ⟨le_of_eq (periodDoublingEdgeMap_dispSq_eq N e),
    periodDoublingEdgeMap_endpoints N e⟩

/-! ## §4. Package (real Props from the headline theorems) -/

/-- The three headline facts assembled as a single Prop, under the side-length
hypothesis `1 < N` required for non-collapse of tetrahedron images. Each
conjunct other than the side-length hypothesis is proved by a named theorem of
this module. Note for assembly: the encoded-torus API
(`EncodedPeriodicFreudenthalTorus`) requires side `2 < N`, so at `N = 2` this
package is typed-skeleton content only; an assembly that routes through the
encoded API must run at side `3` and above. -/
def freudenthal_period_doubling_package (N : ℕ) [NeZero N] : Prop :=
  1 < N ∧
    (∀ (v : Vertex (2 * N) (2 * N) (2 * N)) (dx dy dz : Bool) (a : Fin 8),
        periodDoublingVertexMap N (addBits v dx dy dz) =
            addBits (periodDoublingVertexMap N v) dx dy dz ∧
          periodDoublingVertexMap N (addVertexBits v a) =
            addVertexBits (periodDoublingVertexMap N v) a) ∧
      (∀ (cell : Vertex (2 * N) (2 * N) (2 * N)) (tet : Fin 6),
        (tetVertexSet cell tet).image (periodDoublingVertexMap N) =
            tetVertexSet (periodDoublingVertexMap N cell) tet ∧
          (tetVertexSet (periodDoublingVertexMap N cell) tet).card = 4) ∧
      (∀ e : PeriodicEdge (2 * N) (2 * N) (2 * N),
        periodicDispSqEdge (periodDoublingEdgeMap N e).disp ≤
            periodicDispSqEdge e.disp ∧
          (periodDoublingEdgeMap N e).endpoints =
            (periodDoublingVertexMap N e.endpoints.1,
              periodDoublingVertexMap N e.endpoints.2))

theorem freudenthal_period_doubling_package_holds (N : ℕ) [NeZero N]
    (hN : 1 < N) : freudenthal_period_doubling_package N :=
  ⟨hN,
    fun v dx dy dz a => freudenthal_period_doubling_vertex_map N v dx dy dz a,
    fun cell tet => freudenthal_period_doubling_simplicial_map N hN cell tet,
    fun e => freudenthal_period_doubling_edge_control N e⟩

#print axioms freudenthal_period_doubling_vertex_map
#print axioms freudenthal_period_doubling_simplicial_map
#print axioms freudenthal_period_doubling_edge_control
#print axioms freudenthal_period_doubling_package_holds

end

end Gap2FreudenthalPeriodDoubling
end SevenGaps
end Gravity
end IndisputableMonolith

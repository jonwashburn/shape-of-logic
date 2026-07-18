import Mathlib

/-!
# Glued-Pents Hinge Witness: two 4-simplices sharing a tetrahedron give a PATH link, not a cycle

Panel P1-remainder live bet C12; witness gates whether glued-pent expressions
may be called Regge action.

## What this module witnesses

The concrete two-pent complex: two 4-simplices ("pents")

* `pentA = {0,1,2,3,4}` and `pentB = {0,1,2,3,5}` on the vertex set `Fin 6`,

sharing EXACTLY ONE tetrahedral face `sharedTet = {0,1,2,3}` (proved:
`shared_tets_unique`).  At the chosen hinge triangle `hinge = {0,1,2}` the
incidence data is computed and kernel-checked by `decide`:

* the tetrahedra of the complex containing the hinge are exactly
  `{0,1,2,3}` (in BOTH pents), `{0,1,2,4}` (only in `pentA`), and
  `{0,1,2,5}` (only in `pentB`) — `hingeTets_eq`, `pentA_hinge_tets`,
  `pentB_hinge_tets`, `boundary_tets_belong_to_one_pent`;
* the link of the hinge has vertex set `{3,4,5}` (`linkVerts_eq`) and edge
  set `{{3,4},{3,5}}` (`linkEdges_eq`): each pent containing the hinge
  contributes exactly one link edge, namely its residual vertex pair
  `P \ hinge` (`linkEdges_eq_pent_residues`);
* the two link edges chain through the single shared-tetrahedron vertex 3
  (`link_edges_chain_through_shared`): the link is the PATH `4 — 3 — 5`.

## The honest characterization (do-not-overclaim clause)

**`hinge_link_is_path`**: the hinge link is a path on three vertices with
two edges (endpoint degrees 1, midpoint degree 2:
`linkDegree_four`, `linkDegree_five`, `linkDegree_three`).  It is NOT a
cycle (`hinge_link_not_cycle`).  Therefore the hinge `{0,1,2}` of the
two-pent complex is a BOUNDARY hinge: the dihedral angles at it sum along
an open chain, and any "Regge action"-shaped expression evaluated on this
complex at this hinge is honestly only a *hinge angle-sum*.  A curvature
deficit `2π − Σθ` at this hinge is a boundary (exterior-angle) quantity,
not an interior deficit.

**Why two pents can never do better** (the counting lemma): a cyclic link
in a simple graph needs at least 3 edges (`cycleLink_three_edges`: every
vertex of a cycle has degree 2, and two distinct 2-element edges cannot
close up on two vertices).  Each 4-simplex containing the hinge triangle
contributes exactly one link edge (its residual pair), so a genuine
interior hinge needs at least THREE 4-simplices around the triangle
(`interior_hinge_needs_three_pents`); with two pents it is impossible
(`twoPent_hinge_never_interior`).  The minimal interior-hinge complex is
therefore a cyclic gluing of ≥ 3 pents around the triangle, which this
module does NOT construct; that remains the gate for calling any
glued-pent expression a Regge action.

## Honesty tiers

* THEOREM: every declared theorem below is proved with zero sorry, zero
  admit, zero new axioms; the finite incidence facts are kernel-checked by
  `decide` (no `native_decide`), and `cycleLink_three_edges` /
  `interior_hinge_needs_three_pents` are general structural proofs.
* MODEL: `pentA`, `pentB`, `sharedTet`, `hinge`, `twoPentComplex`, `tets`,
  `hingeTets`, `linkVerts`, `linkEdges`, `linkDegree`, `IsPathLinkOn`,
  `IsCycleLink` are definitional encodings (vertex-set combinatorics of
  the glued complex; simplices as `Finset (Fin 6)`).  This is a purely
  combinatorial layer: no edge lengths, no angles, no analysis.  The
  causal 4-simplex classes of `CausalSimplex4D` carry edge-length data on
  a SINGLE pent; the present module supplies the missing complex-level
  incidence layer and is import-independent of it.

## Relation to the mission wording

Two pents glued along one shared tetrahedron canNOT produce a genuine
interior hinge: the link of the shared triangle is a path (open chain),
not a cycle.  This module states and proves exactly that
(`hinge_link_is_path`, `hinge_link_not_cycle`) and proves the minimal
requirement for an interior hinge (`interior_hinge_needs_three_pents`).
No overclaim: no statement here licenses the phrase "Regge action" for
any two-pent expression.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace GluedPentsHingeWitness

open Finset

/-! ## §1. The two-pent complex (MODEL: concrete combinatorial data) -/

/-- First 4-simplex (pent): vertices `{0,1,2,3,4}`. -/
def pentA : Finset (Fin 6) := {0, 1, 2, 3, 4}

/-- Second 4-simplex (pent): vertices `{0,1,2,3,5}`. -/
def pentB : Finset (Fin 6) := {0, 1, 2, 3, 5}

/-- The shared tetrahedral face `{0,1,2,3}`. -/
def sharedTet : Finset (Fin 6) := {0, 1, 2, 3}

/-- The hinge triangle `{0,1,2}`, a 2-face of the shared tetrahedron. -/
def hinge : Finset (Fin 6) := {0, 1, 2}

/-- The two-pent complex, presented by its maximal simplices. -/
def twoPentComplex : Finset (Finset (Fin 6)) := {pentA, pentB}

/-- All tetrahedra (3-faces) of the complex: the 4-element subsets of the
pents. -/
def tets : Finset (Finset (Fin 6)) :=
  twoPentComplex.biUnion (Finset.powersetCard 4)

/-- The tetrahedra of the complex containing the hinge triangle. -/
def hingeTets : Finset (Finset (Fin 6)) :=
  tets.filter (fun t => hinge ⊆ t)

/-- Link vertices of the hinge: vertices `v ∉ hinge` with
`hinge ∪ {v}` a tetrahedron of the complex. -/
def linkVerts : Finset (Fin 6) :=
  Finset.univ.filter (fun v => v ∉ hinge ∧ insert v hinge ∈ tets)

/-- Link edges of the hinge: vertex pairs `E` disjoint from the hinge with
`hinge ∪ E` a pent of the complex. -/
def linkEdges : Finset (Finset (Fin 6)) :=
  (Finset.univ.powersetCard 2).filter
    (fun E => E ∩ hinge = ∅ ∧ hinge ∪ E ∈ twoPentComplex)

/-- Degree of a vertex in the link graph of the hinge. -/
def linkDegree (v : Fin 6) : ℕ :=
  (linkEdges.filter (fun e => v ∈ e)).card

/-! ## §2. Basic incidence facts (THEOREM, kernel `decide`) -/

/-- THEOREM (by `decide`): both pents are genuine 4-simplices (5 distinct
vertices) and they are distinct. -/
theorem pents_are_distinct_foursimplices :
    pentA.card = 5 ∧ pentB.card = 5 ∧ pentA ≠ pentB := by decide

/-- THEOREM (by `decide`): the pents intersect exactly in the shared
tetrahedron, which has 4 vertices and contains the hinge triangle
(3 vertices). -/
theorem shared_face_data :
    pentA ∩ pentB = sharedTet ∧ sharedTet.card = 4
      ∧ hinge.card = 3 ∧ hinge ⊆ sharedTet := by decide

/-- THEOREM (by `decide`): the pents share EXACTLY ONE tetrahedral face,
namely `sharedTet` (the intersection of their 4-element subset families is
the singleton `{sharedTet}`). -/
theorem shared_tets_unique :
    Finset.powersetCard 4 pentA ∩ Finset.powersetCard 4 pentB
      = {sharedTet} := by decide

/-! ## §3. The hinge incidence data (THEOREM, kernel `decide`) -/

/-- THEOREM (by `decide`): the tetrahedra of the complex containing the
hinge are exactly `{0,1,2,3}`, `{0,1,2,4}`, `{0,1,2,5}`. -/
theorem hingeTets_eq :
    hingeTets
      = {({0, 1, 2, 3} : Finset (Fin 6)), {0, 1, 2, 4}, {0, 1, 2, 5}} := by
  decide

/-- THEOREM (by `decide`): three tetrahedra contain the hinge, and the
shared tetrahedron is one of them. -/
theorem hingeTets_card_and_shared :
    hingeTets.card = 3 ∧ sharedTet ∈ hingeTets := by decide

/-- THEOREM (by `decide`): within `pentA`, the tetrahedra containing the
hinge are `{0,1,2,3}` (shared) and `{0,1,2,4}` (private to `pentA`). -/
theorem pentA_hinge_tets :
    (Finset.powersetCard 4 pentA).filter (fun t => hinge ⊆ t)
      = {({0, 1, 2, 3} : Finset (Fin 6)), {0, 1, 2, 4}} := by decide

/-- THEOREM (by `decide`): within `pentB`, the tetrahedra containing the
hinge are `{0,1,2,3}` (shared) and `{0,1,2,5}` (private to `pentB`). -/
theorem pentB_hinge_tets :
    (Finset.powersetCard 4 pentB).filter (fun t => hinge ⊆ t)
      = {({0, 1, 2, 3} : Finset (Fin 6)), {0, 1, 2, 5}} := by decide

/-- THEOREM (by `decide`): the two non-shared hinge tetrahedra each belong
to exactly one pent (they are BOUNDARY tetrahedra of the complex), while
the shared tetrahedron belongs to both. -/
theorem boundary_tets_belong_to_one_pent :
    (({0, 1, 2, 4} : Finset (Fin 6)) ⊆ pentA
        ∧ ¬ ({0, 1, 2, 4} : Finset (Fin 6)) ⊆ pentB)
      ∧ (({0, 1, 2, 5} : Finset (Fin 6)) ⊆ pentB
        ∧ ¬ ({0, 1, 2, 5} : Finset (Fin 6)) ⊆ pentA)
      ∧ (sharedTet ⊆ pentA ∧ sharedTet ⊆ pentB) := by decide

/-! ## §4. The hinge link: vertex set, edge set, degrees
(THEOREM, kernel `decide`) -/

/-- THEOREM (by `decide`): the link of the hinge has vertex set
`{3, 4, 5}`. -/
theorem linkVerts_eq : linkVerts = {3, 4, 5} := by decide

/-- THEOREM (by `decide`): the link of the hinge has edge set
`{{3,4}, {3,5}}`: one edge per pent (edge `{3,4}` from `pentA`, edge
`{3,5}` from `pentB`), two edges in total. -/
theorem linkEdges_eq :
    linkEdges = {({3, 4} : Finset (Fin 6)), {3, 5}}
      ∧ linkEdges.card = 2 := by decide

/-- THEOREM (by `decide`): the link edges are exactly the residual pairs
`P \ hinge` of the pents — each 4-simplex containing the hinge contributes
exactly one link edge. -/
theorem linkEdges_eq_pent_residues :
    linkEdges = twoPentComplex.image (fun P => P \ hinge)
      ∧ pentA \ hinge = ({3, 4} : Finset (Fin 6))
      ∧ pentB \ hinge = ({3, 5} : Finset (Fin 6)) := by decide

/-- THEOREM (by `decide`): the two link edges chain through the single
residual vertex `3` of the shared tetrahedron: the link is the open chain
`4 — 3 — 5`, hinged at the shared-tet vertex. -/
theorem link_edges_chain_through_shared :
    (({3, 4} : Finset (Fin 6)) ∩ ({3, 5} : Finset (Fin 6)))
        = ({3} : Finset (Fin 6))
      ∧ sharedTet \ hinge = ({3} : Finset (Fin 6)) := by decide

/-- THEOREM (by `decide`): link-graph degrees — midpoint `3` has degree 2,
endpoints `4` and `5` have degree 1.  Degree-1 vertices are exactly what a
cyclic link forbids. -/
theorem linkDegrees :
    linkDegree 3 = 2 ∧ linkDegree 4 = 1 ∧ linkDegree 5 = 1 := by decide

/-! ## §5. The honest characterization: PATH, not cycle -/

/-- The hinge link is a path on the ordered vertices `a — b — c`
(MODEL: definitional path shape for a 3-vertex, 2-edge link). -/
def IsPathLinkOn (a b c : Fin 6) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c
    ∧ linkVerts = {a, b, c}
    ∧ linkEdges = {({a, b} : Finset (Fin 6)), {b, c}}

/-- **THEOREM (main witness, path case)**: the link of the hinge triangle
`{0,1,2}` in the two-pent complex is a PATH: `4 — 3 — 5`, with the
midpoint `3` contributed by the shared tetrahedron.  The hinge is a
BOUNDARY hinge: dihedral angles at it form an open angle-sum, not an
interior deficit. -/
theorem hinge_link_is_path : ∃ a b c : Fin 6, IsPathLinkOn a b c :=
  ⟨4, 3, 5, by unfold IsPathLinkOn; decide⟩

/-- A cyclic link (MODEL: definitional): a nonempty simple edge set, all
edges of size 2, in which EVERY incident vertex has degree exactly 2.
This is the combinatorial condition for the link of a triangle to close up
around the hinge, making the deficit angle `2π − Σθ` an interior
curvature quantity. -/
def IsCycleLink {V : Type*} [DecidableEq V] (E : Finset (Finset V)) : Prop :=
  E.Nonempty ∧ (∀ e ∈ E, e.card = 2)
    ∧ ∀ v : V, (∃ e ∈ E, v ∈ e) → (E.filter (fun e => v ∈ e)).card = 2

/-- **THEOREM (counting lemma)**: a cyclic link needs at least 3 edges.
Proof: take an edge `e = {a,b}`; degree-2 at `a` gives a second edge
`e' ≠ e` through `a`, degree-2 at `b` gives a second edge `e'' ≠ e`
through `b`; if `e' = e''` then it contains both `a` and `b`, and having
exactly 2 elements it would equal `e` — contradiction.  So `e, e', e''`
are three distinct edges. -/
theorem cycleLink_three_edges {V : Type*} [DecidableEq V]
    (E : Finset (Finset V)) (h : IsCycleLink E) : 3 ≤ E.card := by
  obtain ⟨⟨e, he⟩, hcard, hdeg⟩ := h
  obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp (hcard e he)
  have ha : a ∈ e := by
    rw [heab]; exact Finset.mem_insert_self a {b}
  have hb : b ∈ e := by
    rw [heab]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
  -- second edge through a
  have hdega : 1 < (E.filter (fun f => a ∈ f)).card := by
    rw [hdeg a ⟨e, he, ha⟩]; exact one_lt_two
  obtain ⟨e', he'mem, he'ne⟩ := Finset.exists_mem_ne hdega e
  obtain ⟨he'E, hae'⟩ := Finset.mem_filter.mp he'mem
  -- second edge through b
  have hdegb : 1 < (E.filter (fun f => b ∈ f)).card := by
    rw [hdeg b ⟨e, he, hb⟩]; exact one_lt_two
  obtain ⟨e'', he''mem, he''ne⟩ := Finset.exists_mem_ne hdegb e
  obtain ⟨he''E, hbe''⟩ := Finset.mem_filter.mp he''mem
  -- e' and e'' are distinct: otherwise a common edge ⊇ {a,b} of size 2
  -- would equal e
  have hne' : e' ≠ e'' := by
    intro hEq
    have hbe' : b ∈ e' := hEq ▸ hbe''
    have hsub : e ⊆ e' := by
      rw [heab]
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxb
      · exact hxa ▸ hae'
      · exact (Finset.mem_singleton.mp hxb) ▸ hbe'
    have heq : e = e' :=
      Finset.eq_of_subset_of_card_le hsub
        (by rw [hcard e' he'E, hcard e he])
    exact he'ne heq.symm
  -- three distinct edges inside E
  have hnotmem1 : e' ∉ ({e''} : Finset (Finset V)) := by
    intro hmem
    exact hne' (Finset.mem_singleton.mp hmem)
  have hnotmem2 : e ∉ insert e' ({e''} : Finset (Finset V)) := by
    intro hmem
    rcases Finset.mem_insert.mp hmem with hmem' | hmem''
    · exact he'ne hmem'.symm
    · exact he''ne (Finset.mem_singleton.mp hmem'').symm
  have hsub3 : ({e, e', e''} : Finset (Finset V)) ⊆ E := by
    intro f hf
    rcases Finset.mem_insert.mp hf with hf1 | hf'
    · exact hf1 ▸ he
    rcases Finset.mem_insert.mp hf' with hf2 | hf3
    · exact hf2 ▸ he'E
    · exact (Finset.mem_singleton.mp hf3) ▸ he''E
  have hcard3 : ({e, e', e''} : Finset (Finset V)).card = 3 := by
    rw [Finset.card_insert_of_notMem hnotmem2,
      Finset.card_insert_of_notMem hnotmem1, Finset.card_singleton]
  calc 3 = ({e, e', e''} : Finset (Finset V)).card := hcard3.symm
    _ ≤ E.card := Finset.card_le_card hsub3

/-- **THEOREM (minimal interior-hinge requirement)**: since each pent
containing the hinge contributes exactly one link edge (its residual pair
`P \ hinge`), a genuine interior hinge — a cyclic link — requires at least
THREE 4-simplices around the hinge triangle. -/
theorem interior_hinge_needs_three_pents
    (pents : Finset (Finset (Fin 6)))
    (hcycle : IsCycleLink (pents.image (fun P => P \ hinge))) :
    3 ≤ pents.card :=
  le_trans (cycleLink_three_edges _ hcycle) Finset.card_image_le

/-- **THEOREM (main witness, negative case)**: the two-pent complex can
NEVER present the hinge as an interior hinge: its residual link-edge set
(2 edges) cannot be a cycle. -/
theorem twoPent_hinge_never_interior :
    ¬ IsCycleLink (twoPentComplex.image (fun P => P \ hinge)) := by
  intro h
  have h3 := interior_hinge_needs_three_pents twoPentComplex h
  have h2 : twoPentComplex.card = 2 := by decide
  omega

/-- THEOREM: the hinge link of the two-pent complex is not a cycle (stated
directly on `linkEdges` via the residual identification). -/
theorem hinge_link_not_cycle : ¬ IsCycleLink linkEdges := by
  rw [linkEdges_eq_pent_residues.1]
  exact twoPent_hinge_never_interior

/-! ## §6. Axiom audit

`#print axioms` receipts for the load-bearing witnesses.  Expected output:
at most `[propext, Classical.choice, Quot.sound]` (the standard Mathlib
trio; no `sorryAx`, no `Lean.ofReduceBool` from `native_decide`, no
repo-local axioms). -/

#print axioms hinge_link_is_path
#print axioms hinge_link_not_cycle
#print axioms cycleLink_three_edges
#print axioms interior_hinge_needs_three_pents
#print axioms twoPent_hinge_never_interior

end GluedPentsHingeWitness
end SevenGaps
end Gravity
end IndisputableMonolith

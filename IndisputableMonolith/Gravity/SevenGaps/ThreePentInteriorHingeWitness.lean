import IndisputableMonolith.Gravity.SevenGaps.GluedPentsHingeWitness

/-!
# Three-Pent Interior Hinge Witness: the minimal cyclic hinge link

Panel P1-remainder live bet C12; witness gates whether glued-pent expressions
may be called Regge action.  This module supplies the POSITIVE half of the
gate: the minimal complex whose hinge link IS a cycle, complementing the
committed two-pent path witness (`GluedPentsHingeWitness`, whose counting
lemma `interior_hinge_needs_three_pents` proves three pents are necessary).

## The complex

Three 4-simplices ("pents") on the vertex set `Fin 6`, all containing the
hinge triangle `hinge = {0,1,2}` (imported from the two-pent module):

* `pentA = {0,1,2,3,4}` (residual pair `{3,4}`),
* `pentB = {0,1,2,4,5}` (residual pair `{4,5}`),
* `pentC = {0,1,2,3,5}` (residual pair `{3,5}`).

The gluing is face-to-face: each adjacent pair of pents shares EXACTLY ONE
tetrahedron of 4 vertices containing the hinge
(`A ∩ B = {0,1,2,4}`, `B ∩ C = {0,1,2,5}`, `A ∩ C = {0,1,2,3}`;
`pairwise_shared_tets`, `pairwise_shared_tets_unique`), and the triple
intersection is exactly the hinge triangle (`triple_intersection`).

## What is proved (kernel `decide` + structural composition)

* each pent contributes exactly one residual link edge
  (`residual_edges`, `linkEdges_eq_pent_residues`);
* the hinge link has vertex set `{3,4,5}` and edge set
  `{{3,4},{4,5},{3,5}}` — the triangle cycle `3 — 4 — 5 — 3`
  (`linkVerts_eq`, `linkEdges_eq`);
* every link vertex has degree exactly 2 (`linkDegrees`);
* **`threePent_hinge_is_interior`**: the link-edge set satisfies
  `IsCycleLink` (imported cyclic-link predicate) — the hinge `{0,1,2}` is
  a GENUINE INTERIOR hinge of the three-pent complex;
* **`hinge_link_is_cycle`**: the same statement on the module's own
  `linkEdges` via the residual identification;
* **`threePent_minimality`**: this complex has exactly 3 pents and, by the
  committed counting lemma, ANY complex presenting the hinge as interior
  has at least 3 — so this is THE minimal interior-hinge configuration
  (the lower bound is attained).

## Honest scope (do-not-overclaim clause)

MODEL data, THEOREM incidence facts, combinatorial only.  This witness
licenses calling a deficit `2π − Σθ` at this hinge an interior curvature
quantity AT THE INCIDENCE LEVEL: the dihedral angles around the hinge
close up in a cycle, so their sum is compared against a full turn, which
is exactly what "Regge action at an interior hinge" requires
combinatorially.  It does NOT by itself provide edge-length or
causal-structure consistency for three glued CAUSAL pents (consistent
(4,1)/(3,2) edge-length assignments around the cycle, and the resulting
angle values): that metric compatibility question remains OPEN and is a
separate lane.

## Honesty tiers

* THEOREM: every declared theorem below; zero sorry, zero admit, zero new
  axioms; finite incidence facts kernel-checked by `decide`
  (no `native_decide`); the minimality bound composes the committed
  structural lemma `interior_hinge_needs_three_pents`.
* MODEL: `pentA`, `pentB`, `pentC`, `threePentComplex`, `tets`,
  `linkVerts`, `linkEdges`, `linkDegree` are definitional encodings
  (simplices as `Finset (Fin 6)`), mirroring the committed two-pent
  module's representation with the hinge `{0,1,2}` shared literally.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ThreePentInteriorHingeWitness

open Finset
open GluedPentsHingeWitness (hinge IsCycleLink cycleLink_three_edges
  interior_hinge_needs_three_pents)

/-! ## §1. The three-pent complex (MODEL: concrete combinatorial data) -/

/-- First pent: vertices `{0,1,2,3,4}`, residual pair `{3,4}`. -/
def pentA : Finset (Fin 6) := {0, 1, 2, 3, 4}

/-- Second pent: vertices `{0,1,2,4,5}`, residual pair `{4,5}`. -/
def pentB : Finset (Fin 6) := {0, 1, 2, 4, 5}

/-- Third pent: vertices `{0,1,2,3,5}`, residual pair `{3,5}`. -/
def pentC : Finset (Fin 6) := {0, 1, 2, 3, 5}

/-- The three-pent complex, presented by its maximal simplices. -/
def threePentComplex : Finset (Finset (Fin 6)) := {pentA, pentB, pentC}

/-- All tetrahedra (3-faces) of the complex: the 4-element subsets of the
pents. -/
def tets : Finset (Finset (Fin 6)) :=
  threePentComplex.biUnion (Finset.powersetCard 4)

/-- Link vertices of the hinge: vertices `v ∉ hinge` with
`hinge ∪ {v}` a tetrahedron of the complex. -/
def linkVerts : Finset (Fin 6) :=
  Finset.univ.filter (fun v => v ∉ hinge ∧ insert v hinge ∈ tets)

/-- Link edges of the hinge: vertex pairs `E` disjoint from the hinge with
`hinge ∪ E` a pent of the complex (same definition shape as the committed
two-pent module, adapted to `threePentComplex`). -/
def linkEdges : Finset (Finset (Fin 6)) :=
  (Finset.univ.powersetCard 2).filter
    (fun E => E ∩ hinge = ∅ ∧ hinge ∪ E ∈ threePentComplex)

/-- Degree of a vertex in the link graph of the hinge. -/
def linkDegree (v : Fin 6) : ℕ :=
  (linkEdges.filter (fun e => v ∈ e)).card

/-! ## §2. Face-to-face gluing data (THEOREM, kernel `decide`) -/

/-- THEOREM (by `decide`): all three pents are genuine 4-simplices
(5 distinct vertices each) and are pairwise distinct, and each contains
the hinge. -/
theorem pents_are_distinct_foursimplices :
    pentA.card = 5 ∧ pentB.card = 5 ∧ pentC.card = 5
      ∧ pentA ≠ pentB ∧ pentB ≠ pentC ∧ pentA ≠ pentC
      ∧ hinge ⊆ pentA ∧ hinge ⊆ pentB ∧ hinge ⊆ pentC := by decide

/-- THEOREM (by `decide`): each adjacent pair of pents intersects in a
tetrahedron (4 vertices) containing the hinge — the gluing is
face-to-face around the hinge. -/
theorem pairwise_shared_tets :
    (pentA ∩ pentB = ({0, 1, 2, 4} : Finset (Fin 6))
        ∧ (pentA ∩ pentB).card = 4 ∧ hinge ⊆ pentA ∩ pentB)
      ∧ (pentB ∩ pentC = ({0, 1, 2, 5} : Finset (Fin 6))
        ∧ (pentB ∩ pentC).card = 4 ∧ hinge ⊆ pentB ∩ pentC)
      ∧ (pentA ∩ pentC = ({0, 1, 2, 3} : Finset (Fin 6))
        ∧ (pentA ∩ pentC).card = 4 ∧ hinge ⊆ pentA ∩ pentC) := by decide

/-- THEOREM (by `decide`): each pair of pents shares EXACTLY ONE
tetrahedral face (the intersection of their 4-element subset families is
a singleton). -/
theorem pairwise_shared_tets_unique :
    Finset.powersetCard 4 pentA ∩ Finset.powersetCard 4 pentB
        = {({0, 1, 2, 4} : Finset (Fin 6))}
      ∧ Finset.powersetCard 4 pentB ∩ Finset.powersetCard 4 pentC
        = {({0, 1, 2, 5} : Finset (Fin 6))}
      ∧ Finset.powersetCard 4 pentA ∩ Finset.powersetCard 4 pentC
        = {({0, 1, 2, 3} : Finset (Fin 6))} := by decide

/-- THEOREM (by `decide`): the triple intersection of the three pents is
exactly the hinge triangle — the three pents wrap around the hinge and
nothing more. -/
theorem triple_intersection : pentA ∩ pentB ∩ pentC = hinge := by decide

/-! ## §3. The hinge link: the triangle cycle (THEOREM, kernel `decide`) -/

/-- THEOREM (by `decide`): each pent contributes exactly one residual link
edge. -/
theorem residual_edges :
    pentA \ hinge = ({3, 4} : Finset (Fin 6))
      ∧ pentB \ hinge = ({4, 5} : Finset (Fin 6))
      ∧ pentC \ hinge = ({3, 5} : Finset (Fin 6)) := by decide

/-- THEOREM (by `decide`): the link of the hinge has vertex set
`{3, 4, 5}`. -/
theorem linkVerts_eq : linkVerts = {3, 4, 5} := by decide

/-- THEOREM (by `decide`): the link of the hinge has edge set
`{{3,4}, {4,5}, {3,5}}` — the triangle cycle `3 — 4 — 5 — 3` — with one
edge per pent, three edges in total. -/
theorem linkEdges_eq :
    linkEdges = {({3, 4} : Finset (Fin 6)), {4, 5}, {3, 5}}
      ∧ linkEdges.card = 3 := by decide

/-- THEOREM (by `decide`): the link edges are exactly the residual pairs
`P \ hinge` of the pents. -/
theorem linkEdges_eq_pent_residues :
    linkEdges = threePentComplex.image (fun P => P \ hinge) := by decide

/-- THEOREM (by `decide`): every link vertex has degree exactly 2 — the
closed-chain condition a boundary hinge fails (the two-pent path witness
had endpoint degrees 1). -/
theorem linkDegrees :
    linkDegree 3 = 2 ∧ linkDegree 4 = 2 ∧ linkDegree 5 = 2 := by decide

/-! ## §4. The headline: genuine interior hinge, and minimality -/

/-- **THEOREM (main witness, cycle case)**: the residual link-edge set of
the three-pent complex satisfies `IsCycleLink` — the hinge `{0,1,2}` is a
GENUINE INTERIOR hinge.  At the incidence level this is exactly what a
Regge deficit `2π − Σθ` at the hinge requires: the dihedral angles close
up in a cycle around the hinge. -/
theorem threePent_hinge_is_interior :
    IsCycleLink (threePentComplex.image (fun P => P \ hinge)) := by
  unfold IsCycleLink
  decide

/-- THEOREM: the same statement on this module's `linkEdges`, via the
residual identification. -/
theorem hinge_link_is_cycle : IsCycleLink linkEdges := by
  rw [linkEdges_eq_pent_residues]
  exact threePent_hinge_is_interior

/-- **THEOREM (minimality)**: the three-pent complex attains the proved
lower bound: it has exactly 3 pents, and by the committed counting lemma
(`interior_hinge_needs_three_pents`) ANY family of pents presenting the
hinge as interior has at least 3.  This is THE minimal interior-hinge
configuration. -/
theorem threePent_minimality :
    threePentComplex.card = 3
      ∧ (∀ pents : Finset (Finset (Fin 6)),
          IsCycleLink (pents.image (fun P => P \ hinge)) → 3 ≤ pents.card) :=
  ⟨by decide, fun pents h => interior_hinge_needs_three_pents pents h⟩

/-! ## §5. Axiom audit

`#print axioms` receipts for the load-bearing witnesses.  Expected output:
at most `[propext, Classical.choice, Quot.sound]` (the standard Mathlib
trio; no `sorryAx`, no `Lean.ofReduceBool` from `native_decide`, no
repo-local axioms). -/

#print axioms threePent_hinge_is_interior
#print axioms hinge_link_is_cycle
#print axioms threePent_minimality
#print axioms linkEdges_eq
#print axioms linkDegrees

end ThreePentInteriorHingeWitness
end SevenGaps
end Gravity
end IndisputableMonolith

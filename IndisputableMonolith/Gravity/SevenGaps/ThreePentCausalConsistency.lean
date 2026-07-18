import IndisputableMonolith.Gravity.SevenGaps.ThreePentInteriorHingeWitness
import IndisputableMonolith.Gravity.SevenGaps.CausalSimplex4D

/-!
# Three-Pent Causal Consistency: an explicit admissible causal edge-length
# assignment on the minimal interior-hinge complex (gap6-a, W3-2)

QG full-theory campaign, Wave 3 lane W3-2.  `ThreePentInteriorHingeWitness`
proved the minimal genuine interior hinge exists COMBINATORIALLY and its
honest-scope clause named exactly what was missing: consistent causal edge
lengths around the cycle.  This module supplies them.

## The assignment (MODEL data, one global function)

Slice structure on the six vertices: the hinge triangle `{0,1,2}` lies on
slice `t` (`slice6 = false`), the three link vertices `{3,4,5}` on slice
`t+1` (`slice6 = true`).  ONE global squared-length function on vertex
pairs (`causalSqLength`): same-slice pairs carry `a^2` (spacelike),
cross-slice pairs carry `-(alpha * a^2)` (timelike).  Because every pent
pulls its edge tuple back from this single function, cycle consistency is
structural: adjacent pents agree on shared faces by construction
(`shared_face_consistency` states it as a kernel theorem).

## What is proved (THEOREM)

* `induced_pentA_eq` / `induced_pentB_eq` / `induced_pentC_eq` — the
  heart: each of the three pents, enumerated by its order-preserving
  vertex chart, pulls the global assignment back to EXACTLY the standard
  CDT Lorentzian (3,2) tuple `lorentzianSqEdges threeTwo a alpha` of the
  kernel-checked `CausalSimplex4D` layer.  The three-pent complex is
  literally three standard causal (3,2) pents glued around the hinge.
* `pent_charts_cover` / `pent_charts_injective` /
  `pent_slices_match` — the charts enumerate the witness module's own
  pents (`decide`), injectively, and carry slice `t`/`t+1` exactly onto
  the (3,2) slice structure of `CausalSimplex4D.sliceOf`.
* `threePent_lorentzian_class` — each induced tuple is a member of the
  Lorentzian causal class (`LorentzianClass threeTwo`).
* `threePent_lorentzian_cm4_neg` — per-pent Lorentzian Cayley-Menger
  certificate: `cm4 = -((12*alpha + 7) * a^8) < 0` on every pent
  (`0 < a`, `0 ≤ alpha`).
* `threePent_euclidean_admissible` — per-pent Euclidean admissibility
  after Wick: `cm4 (wick threeTwo ·) > 0` for every pent on the EXACT
  CDT range `alpha > 7/12` (`alphaMin threeTwo`); thresholds inherited
  exact from `CausalSimplex4D`.
* `hinge_edges_spacelike` / `link_edges_spacelike` /
  `cross_edges_timelike` — causal-type certificates: the hinge triangle
  and the link cycle `3-4-5-3` are spacelike, all nine hinge-to-link
  edges timelike.
* `physical_point_regular` — non-vacuity anchor: at `a = 1`, `alpha = 1`
  every pent Wick-rotates to the regular unit 4-simplex, `cm4 = 5`.
* `threePent_causal_assignment` — the packaged headline: on `0 < a`,
  `7/12 < alpha`, the explicit assignment simultaneously presents all
  three pents as admissible causal (3,2) simplices.

## Consequence for the campaign (existence-only; critic-tightened scope)

Gap6-a in its EXISTENTIAL reading is CLOSED POSITIVE: an admissible
causal edge-length assignment on the minimal interior-hinge complex
EXISTS explicitly, so the certified-NON-EXISTENCE branch of the W3-2
lane (which would have stopped gap6-b) does not fire.  What is realized
is THE symmetric standard CDT slab assignment (lengths depend only on
same-slice vs cross-slice); the classification of ASYMMETRIC assignments
around the hinge cycle, and any monodromy obstruction theory for
non-standard per-pent data, are NOT addressed and remain open questions
outside this lane's contract.  The action-level continuation lane
(gap6-b, W4-3 `WickActionInteriorHinge`) now has a concrete causal
object to attack: three (3,2) pents whose hinge data continuation
certificates are already landed per pent (`WickThreeTwoHinges`, B2).
This module does NOT do gap6-b and does NOT touch any
`FullTheoryLedger` flag; `gap6_lorentzian_action` stays `false`.

## Inherited disclosure (binding, from `CausalSimplex4D`)

"Admissible" is the Cayley-Menger positivity criterion `cm4 > 0` after
Wick (equivalently `9216 * V^2 > 0`), the exact 4d CDT regime.  The
classical equivalence "cm4 > 0 iff embeddable in R^4" is NOT formalized
in this repo for n = 4; under that classical reading the Euclideanized
pents are genuine nondegenerate 4-simplices.  The dihedral ANGLE VALUES
around the hinge (needed for the deficit) are gap6-b's business, not
claimed here.

No `sorry`, no `admit`, no new axioms, no `native_decide` (`decide`
only, on finite Bool/Finset data), no `: True` or `Nonempty`-only
headline.  Expected axiom footprint of every theorem: the standard trio
`[propext, Classical.choice, Quot.sound]`.  Receipts at end of file.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace ThreePentCausalConsistency

open CausalSimplex4D

noncomputable section

/-! ## §1. The global causal assignment (MODEL) -/

/-- Slice membership of the six vertices: hinge `{0,1,2}` on slice `t`
(`false`), link vertices `{3,4,5}` on slice `t+1` (`true`). -/
def slice6 : Fin 6 → Bool
  | 0 => false | 1 => false | 2 => false
  | 3 => true | 4 => true | 5 => true

/-- THE global causal squared-length assignment on vertex pairs:
same-slice pairs are spacelike (`a^2`), cross-slice pairs timelike
(`-(alpha * a^2)`).  Every pent pulls its edge tuple back from this ONE
function, so shared faces agree by construction. -/
def causalSqLength (a alpha : ℝ) (u v : Fin 6) : ℝ :=
  if slice6 u != slice6 v then -(alpha * a ^ 2) else a ^ 2

/-- The assignment is symmetric in its vertex pair. -/
theorem causalSqLength_symm (a alpha : ℝ) (u v : Fin 6) :
    causalSqLength a alpha u v = causalSqLength a alpha v u := by
  unfold causalSqLength
  cases hu : slice6 u <;> cases hv : slice6 v <;> simp

/-! ## §2. The three pent charts and their incidence certificates -/

/-- Vertex chart of pent `A = {0,1,2,3,4}` (order-preserving). -/
def pentAVert : Fin 5 → Fin 6
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4

/-- Vertex chart of pent `B = {0,1,2,4,5}` (order-preserving). -/
def pentBVert : Fin 5 → Fin 6
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 5

/-- Vertex chart of pent `C = {0,1,2,3,5}` (order-preserving). -/
def pentCVert : Fin 5 → Fin 6
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5

/-- THEOREM (by `decide`): the three charts enumerate exactly the witness
module's pents. -/
theorem pent_charts_cover :
    Finset.univ.image pentAVert = ThreePentInteriorHingeWitness.pentA
      ∧ Finset.univ.image pentBVert = ThreePentInteriorHingeWitness.pentB
      ∧ Finset.univ.image pentCVert = ThreePentInteriorHingeWitness.pentC := by
  decide

/-- THEOREM (by `decide`): each chart is injective (five distinct
vertices; genuine 4-simplices). -/
theorem pent_charts_injective :
    Function.Injective pentAVert ∧ Function.Injective pentBVert
      ∧ Function.Injective pentCVert := by
  decide

/-- THEOREM (by `decide`): every chart carries the global slice structure
exactly onto the (3,2) slice structure of the causal 4-simplex layer —
each pent has its `{0,1,2}` face on slice `t` and its residual pair on
slice `t+1`, which is the (3,2) causal type. -/
theorem pent_slices_match :
    (∀ v : Fin 5, slice6 (pentAVert v) = sliceOf CausalPentType.threeTwo v)
      ∧ (∀ v : Fin 5,
        slice6 (pentBVert v) = sliceOf CausalPentType.threeTwo v)
      ∧ (∀ v : Fin 5,
        slice6 (pentCVert v) = sliceOf CausalPentType.threeTwo v) := by
  decide

/-! ## §3. The induced edge tuples ARE the standard causal (3,2) tuples -/

/-- The squared-edge tuple a pent chart pulls back from the global
assignment. -/
def inducedSqEdges (verts : Fin 5 → Fin 6) (a alpha : ℝ) :
    SqEdges10 :=
  fun e =>
    causalSqLength a alpha (verts (pentEdgeVertices e).1)
      (verts (pentEdgeVertices e).2)

/-- Shared-face consistency, structurally: whenever two charts send edge
indices to the same global vertex pair (in either order), the induced
squared lengths agree.  This is the "consistent around the cycle"
statement: there is one global length per edge of the complex, full
stop. -/
theorem shared_face_consistency (a alpha : ℝ) (P Q : Fin 5 → Fin 6)
    (e e' : Fin 10)
    (h : (P (pentEdgeVertices e).1 = Q (pentEdgeVertices e').1
          ∧ P (pentEdgeVertices e).2 = Q (pentEdgeVertices e').2)
        ∨ (P (pentEdgeVertices e).1 = Q (pentEdgeVertices e').2
          ∧ P (pentEdgeVertices e).2 = Q (pentEdgeVertices e').1)) :
    inducedSqEdges P a alpha e = inducedSqEdges Q a alpha e' := by
  unfold inducedSqEdges
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, causalSqLength_symm]

/-- **THEOREM (consistency core, pent A): the induced tuple of pent A is
EXACTLY the standard CDT Lorentzian (3,2) tuple.** -/
theorem induced_pentA_eq (a alpha : ℝ) :
    inducedSqEdges pentAVert a alpha =
      lorentzianSqEdges CausalPentType.threeTwo a alpha := by
  funext e
  fin_cases e <;> rfl

/-- **THEOREM (consistency core, pent B).** -/
theorem induced_pentB_eq (a alpha : ℝ) :
    inducedSqEdges pentBVert a alpha =
      lorentzianSqEdges CausalPentType.threeTwo a alpha := by
  funext e
  fin_cases e <;> rfl

/-- **THEOREM (consistency core, pent C).** -/
theorem induced_pentC_eq (a alpha : ℝ) :
    inducedSqEdges pentCVert a alpha =
      lorentzianSqEdges CausalPentType.threeTwo a alpha := by
  funext e
  fin_cases e <;> rfl

/-! ## §4. Per-pent certificates (Lorentzian class, Cayley-Menger, Wick) -/

/-- THEOREM: each induced tuple is a member of the Lorentzian causal
class of type (3,2). -/
theorem threePent_lorentzian_class (a alpha : ℝ) (ha : 0 < a)
    (halpha : 0 < alpha) :
    inducedSqEdges pentAVert a alpha ∈ LorentzianClass CausalPentType.threeTwo
      ∧ inducedSqEdges pentBVert a alpha
          ∈ LorentzianClass CausalPentType.threeTwo
      ∧ inducedSqEdges pentCVert a alpha
          ∈ LorentzianClass CausalPentType.threeTwo :=
  ⟨⟨a, alpha, ha, halpha, induced_pentA_eq a alpha⟩,
    ⟨a, alpha, ha, halpha, induced_pentB_eq a alpha⟩,
    ⟨a, alpha, ha, halpha, induced_pentC_eq a alpha⟩⟩

/-- THEOREM (per-pent Lorentzian Cayley-Menger certificate): every pent
of the complex has `cm4 = -((12*alpha + 7) * a^8) < 0` — the strict CM
negativity of a genuine Lorentzian (3,2) simplex. -/
theorem threePent_lorentzian_cm4_neg (a alpha : ℝ) (ha : 0 < a)
    (halpha : 0 ≤ alpha) :
    cm4 (inducedSqEdges pentAVert a alpha) < 0
      ∧ cm4 (inducedSqEdges pentBVert a alpha) < 0
      ∧ cm4 (inducedSqEdges pentCVert a alpha) < 0 := by
  rw [induced_pentA_eq, induced_pentB_eq, induced_pentC_eq]
  have h := lorentzian_cm4_neg_threeTwo a alpha ha halpha
  exact ⟨h, h, h⟩

/-- THEOREM (per-pent Euclidean admissibility): on the EXACT 4d CDT
range `alpha > 7/12` (with `0 < a`), the Wick image of every pent
satisfies the Cayley-Menger positivity criterion `cm4 > 0` — all three
pents Euclideanize to nondegenerate 4-simplices simultaneously. -/
theorem threePent_euclidean_admissible (a alpha : ℝ) (ha : 0 < a)
    (halpha : 7 / 12 < alpha) :
    0 < cm4 (wick CausalPentType.threeTwo (inducedSqEdges pentAVert a alpha))
      ∧ 0 < cm4 (wick CausalPentType.threeTwo
          (inducedSqEdges pentBVert a alpha))
      ∧ 0 < cm4 (wick CausalPentType.threeTwo
          (inducedSqEdges pentCVert a alpha)) := by
  rw [induced_pentA_eq, induced_pentB_eq, induced_pentC_eq]
  have h := wick_lorentzian_nondegenerate CausalPentType.threeTwo a alpha ha
    (by rw [alphaMin_threeTwo]; exact halpha)
  exact ⟨h, h, h⟩

/-! ## §5. Causal-type certificates on the complex -/

/-- THEOREM: the three hinge edges `{0,1}, {0,2}, {1,2}` are spacelike
(squared length `a^2`). -/
theorem hinge_edges_spacelike (a alpha : ℝ) :
    causalSqLength a alpha 0 1 = a ^ 2
      ∧ causalSqLength a alpha 0 2 = a ^ 2
      ∧ causalSqLength a alpha 1 2 = a ^ 2 :=
  ⟨rfl, rfl, rfl⟩

/-- THEOREM: the three link-cycle edges `{3,4}, {4,5}, {3,5}` (one per
pent: the residual pair) are spacelike (squared length `a^2`) — the
hinge link `3-4-5-3` is a spacelike cycle on slice `t+1`. -/
theorem link_edges_spacelike (a alpha : ℝ) :
    causalSqLength a alpha 3 4 = a ^ 2
      ∧ causalSqLength a alpha 4 5 = a ^ 2
      ∧ causalSqLength a alpha 3 5 = a ^ 2 :=
  ⟨rfl, rfl, rfl⟩

/-- THEOREM: all nine hinge-to-link edges are timelike (squared length
`-(alpha * a^2)`). -/
theorem cross_edges_timelike (a alpha : ℝ) :
    ∀ u v : Fin 6, u ∈ GluedPentsHingeWitness.hinge →
      v ∈ ThreePentInteriorHingeWitness.linkVerts →
      causalSqLength a alpha u v = -(alpha * a ^ 2) := by
  intro u v hu hv
  fin_cases u <;> fin_cases v <;>
    first
      | rfl
      | exact absurd hu (by decide)
      | exact absurd hv (by decide)

/-! ## §6. Physical-point anchor and the packaged headline -/

/-- THEOREM (non-vacuity anchor): at the physical point `a = 1`,
`alpha = 1`, every pent of the complex Wick-rotates to the regular unit
4-simplex, `cm4 = 5`. -/
theorem physical_point_regular :
    wick CausalPentType.threeTwo (inducedSqEdges pentAVert 1 1)
        = (fun _ => (1 : ℝ))
      ∧ cm4 (wick CausalPentType.threeTwo (inducedSqEdges pentAVert 1 1)) = 5
      ∧ wick CausalPentType.threeTwo (inducedSqEdges pentBVert 1 1)
          = (fun _ => (1 : ℝ))
      ∧ wick CausalPentType.threeTwo (inducedSqEdges pentCVert 1 1)
          = (fun _ => (1 : ℝ)) := by
  have hA : wick CausalPentType.threeTwo (inducedSqEdges pentAVert 1 1)
      = (fun _ => (1 : ℝ)) := by
    rw [induced_pentA_eq, wick_lorentzian,
      euclideanSqEdges_alpha_one CausalPentType.threeTwo]
  have hB : wick CausalPentType.threeTwo (inducedSqEdges pentBVert 1 1)
      = (fun _ => (1 : ℝ)) := by
    rw [induced_pentB_eq, wick_lorentzian,
      euclideanSqEdges_alpha_one CausalPentType.threeTwo]
  have hC : wick CausalPentType.threeTwo (inducedSqEdges pentCVert 1 1)
      = (fun _ => (1 : ℝ)) := by
    rw [induced_pentC_eq, wick_lorentzian,
      euclideanSqEdges_alpha_one CausalPentType.threeTwo]
  exact ⟨hA, by rw [hA]; exact cm4_regular_unit, hB, hC⟩

/-- **GAP6-A HEADLINE (THEOREM): an explicit admissible causal
edge-length assignment on the minimal three-pent interior-hinge complex
EXISTS.**  On the exact 4d CDT range (`0 < a`, `alpha > 7/12`), the ONE
global assignment `causalSqLength` presents all three pents
simultaneously as standard Lorentzian (3,2) simplices (consistency
core), members of the Lorentzian causal class, with strict Lorentzian
CM negativity and Euclidean CM admissibility after Wick, per pent.
EXISTENCE-ONLY SCOPE: this realizes the symmetric standard CDT slab
assignment; it does not classify asymmetric assignments or hinge-cycle
monodromy.  The certified-non-existence branch of the W3-2 lane does
not fire; gap6-b may proceed against this concrete object. -/
theorem threePent_causal_assignment (a alpha : ℝ) (ha : 0 < a)
    (halpha : 7 / 12 < alpha) :
    (inducedSqEdges pentAVert a alpha
          = lorentzianSqEdges CausalPentType.threeTwo a alpha
        ∧ inducedSqEdges pentBVert a alpha
          = lorentzianSqEdges CausalPentType.threeTwo a alpha
        ∧ inducedSqEdges pentCVert a alpha
          = lorentzianSqEdges CausalPentType.threeTwo a alpha)
      ∧ (inducedSqEdges pentAVert a alpha
            ∈ LorentzianClass CausalPentType.threeTwo
        ∧ inducedSqEdges pentBVert a alpha
            ∈ LorentzianClass CausalPentType.threeTwo
        ∧ inducedSqEdges pentCVert a alpha
            ∈ LorentzianClass CausalPentType.threeTwo)
      ∧ (cm4 (inducedSqEdges pentAVert a alpha) < 0
        ∧ cm4 (inducedSqEdges pentBVert a alpha) < 0
        ∧ cm4 (inducedSqEdges pentCVert a alpha) < 0)
      ∧ (0 < cm4 (wick CausalPentType.threeTwo
            (inducedSqEdges pentAVert a alpha))
        ∧ 0 < cm4 (wick CausalPentType.threeTwo
            (inducedSqEdges pentBVert a alpha))
        ∧ 0 < cm4 (wick CausalPentType.threeTwo
            (inducedSqEdges pentCVert a alpha))) := by
  have halpha0 : 0 < alpha := lt_trans (by norm_num) halpha
  exact ⟨⟨induced_pentA_eq a alpha, induced_pentB_eq a alpha,
      induced_pentC_eq a alpha⟩,
    threePent_lorentzian_class a alpha ha halpha0,
    threePent_lorentzian_cm4_neg a alpha ha halpha0.le,
    threePent_euclidean_admissible a alpha ha halpha⟩

/-! ## §7. Axiom audit

Expected for each: `[propext, Classical.choice, Quot.sound]` (no
`sorryAx`, no `Lean.ofReduceBool`, no repo-local axioms). -/

#print axioms induced_pentA_eq
#print axioms induced_pentB_eq
#print axioms induced_pentC_eq
#print axioms shared_face_consistency
#print axioms threePent_lorentzian_cm4_neg
#print axioms threePent_euclidean_admissible
#print axioms threePent_causal_assignment
#print axioms physical_point_regular

end

end ThreePentCausalConsistency
end SevenGaps
end Gravity
end IndisputableMonolith

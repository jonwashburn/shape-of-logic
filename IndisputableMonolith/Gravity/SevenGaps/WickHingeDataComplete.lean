import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import IndisputableMonolith.Gravity.SevenGaps.WickActionComplexFirst
import IndisputableMonolith.Gravity.SevenGaps.WickFourOneAllHinges
import IndisputableMonolith.Gravity.SevenGaps.WickThreeTwoHinges

/-!
# Hinge-Data Wick Continuation, Complete Over Both Causal Types (Lane B3)

QG Seven-Gaps campaign, lane B of the finishing charter, third deliverable:
the conjunction of the per-type certificates into a single completeness
statement over BOTH causal 4-simplex types and ALL twenty hinges.

## Honest scope (MANDATED disclosure; read before citing this theorem)

This is a **hinge-DATA continuation**: what is certified is the continuation
of the dihedral cosines and areas-squared of the triangular hinges of a
SINGLE causal 4-simplex of each type, along the canonical upper-half-plane
arc at the physical point `a = 1`, `alpha = 1`.  It is NOT an action-level
continuation.  The ACTION-LEVEL continuation (deficit angles summed over
the simplices sharing an interior hinge, hence the continued Regge action
itself) remains **OPEN**: it requires a genuine three-or-more-pent
interior-hinge simplicial complex, which is the C12 lane's prerequisite
question and is not touched here.  NO `FullTheoryLedger` flag is changed by
this module; `causalSimplex4DStatus.action_level_continuation_open` remains
`true`.

## What the three packaged theorems state

`wick_hinge_data_continuation_complete` (COSINE continuation) states, for
every unordered vertex pair `{p, q}` of `Fin 5` (equivalently every
triangular hinge, the complementary triple) and BOTH causal types:

* fourOne: `BranchRegularOn` on the FULL open arc interior, continuity of
  the split-form cosine on the CLOSED interval `[0,1]`, and the Euclidean
  endpoint value `-(1/4)` (from `WickFourOneAllHinges`, B1);
* threeTwo: the same three certificates (from `WickThreeTwoHinges`, B2).

`wick_hinge_areaSq_closed_forms_complete` (AREAS-SQUARED) states the
closed form of the area-squared of ALL twenty hinges, for every `z`:
`3/16` on the all-spacelike classes, `z/4 - 1/16` on the classes with
timelike edges (cut avoidance on the open interior is
`WickFourOneAllHinges.fourOne_areaSq_interior_off_cut`, the same two
closed forms).

`wick_product_form_kills_memorialized` (KILL certificates) packages the
two exact product-form crossings: the diagonal-cofactor PRODUCT lands ON
the `csqrt` cut at interior arc parameters, value `-40` at `tStarMixed`
(mixed class, `Re z = 5/12`) and `-48` at `t = 2/3` exactly (upper-pair
class).  These memorialize the gate FAIL of the single-sqrt product
transcription; the split-sqrt form is the repaired convention.

Endpoint honesty (inherited, not weakened here): branch certificates are
interior-only because several hinge data sit exactly ON a cut at the
Lorentzian endpoint (fourOne timelike-class cofactor `-8`; timelike-shape
`areaSq = -5/16`; the threeTwo spacelike hinge cosine `-11/8` ON the arccos
cut).  All are ALLOWED endpoint contacts under the executed gate
(`state/qg_full_theory/wick_arc_trace/RESULTS.txt`); the endpoint VALUES
are exact because each split cosine is proved continuous on `[0,1]`.
The Lorentzian endpoint carries the documented split-form sign factor
(`WickActionComplexFirst.lorentzian_endpoint_sign_factor`); no unrestricted
equality with the real Lorentzian formula is claimed.

## Honesty tiers

* MODEL: nothing new; all definitions inherited from
  `WickActionComplexFirst`, `WickFourOneAllHinges`, `WickThreeTwoHinges`.
* THEOREM: `wick_hinge_data_continuation_complete`,
  `wick_hinge_areaSq_closed_forms_complete`,
  `wick_product_form_kills_memorialized` (kernel-checked conjunctions of
  the B1 and B2 results; sorry-free).
* OPEN: the action-level continuation (C12 lane), exactly as flagged in
  `CausalSimplex4D.causalSimplex4DStatus`.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace WickHingeDataComplete

open CausalSimplex4D
open WickActionComplexFirst
open WickFourOneAllHinges
open WickThreeTwoHinges

/-- THEOREM (B3 headline, hinge-DATA continuation, complete): for EVERY
triangular hinge (every unordered opposite vertex pair `{p, q}`, both
orientations) of BOTH causal 4-simplex types, at the physical point
`a = 1`, `alpha = 1`, the split-form complex-first Wick continuation is
(i) branch-regular on the FULL open arc interior `Set.Ioo 0 1` and
(ii) a continuous path on the CLOSED interval `[0, 1]` ending at the
Euclidean regular-4-simplex cosine `-(1/4)`.

SCOPE: hinge data (dihedral cosines and areas-squared of single-simplex
hinges) ONLY.  The action-level continuation stays OPEN (the C12
three-pent interior-hinge complex is its prerequisite); no
`FullTheoryLedger` flag is touched by this result. -/
theorem wick_hinge_data_continuation_complete :
    ∀ p q : Fin 5, p ≠ q →
      (BranchRegularOn
          (fun t => continuationEdgesC CausalPentType.fourOne 1 1 t) p q
          (Set.Ioo 0 1)
        ∧ ContinuousOn (fourOneCosPath p q) (Set.Icc 0 1)
        ∧ fourOneCosPath p q 1 = -(1 / 4 : ℂ))
      ∧ (BranchRegularOn
          (fun t => continuationEdgesC CausalPentType.threeTwo 1 1 t) p q
          (Set.Ioo 0 1)
        ∧ ContinuousOn (threeTwoCosPath p q) (Set.Icc 0 1)
        ∧ threeTwoCosPath p q 1 = -(1 / 4 : ℂ)) := by
  intro p q hpq
  obtain ⟨h41cont, h41end⟩ :=
    wick_boundary_continuation_fourOne_allHinges p q hpq
  obtain ⟨h32branch, h32cont, h32end⟩ :=
    wick_continuation_threeTwo_hinges p q hpq
  exact ⟨⟨branchRegular_fourOne_allHinges p q hpq, h41cont, h41end⟩,
    ⟨h32branch, h32cont, h32end⟩⟩

/-- THEOREM (B3, areas-squared complete): the closed forms of ALL twenty
hinge areas-squared, both causal types, for every `z`: `3/16` on the
all-spacelike classes, `z/4 - 1/16` on every class with timelike edges.
Cut avoidance on the open arc interior is
`WickFourOneAllHinges.fourOne_areaSq_interior_off_cut` (identical two
closed forms; the `-5/16` Lorentzian endpoint contact is the documented
allowed contact). -/
theorem wick_hinge_areaSq_closed_forms_complete (z : ℂ) :
    (hingeAreaSqC (hingeEdgesC z) 0 1 2 = (3 / 16 : ℂ)
        ∧ hingeAreaSqC (hingeEdgesC z) 0 1 3 = (3 / 16 : ℂ)
        ∧ hingeAreaSqC (hingeEdgesC z) 0 2 3 = (3 / 16 : ℂ)
        ∧ hingeAreaSqC (hingeEdgesC z) 1 2 3 = (3 / 16 : ℂ))
      ∧ (hingeAreaSqC (hingeEdgesC z) 0 1 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdgesC z) 0 2 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdgesC z) 0 3 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdgesC z) 1 2 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdgesC z) 1 3 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdgesC z) 2 3 4 = z / 4 - 1 / 16)
      ∧ (hingeAreaSqC (hingeEdges32C z) 0 1 2 = (3 / 16 : ℂ)
        ∧ hingeAreaSqC (hingeEdges32C z) 0 1 3 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 0 1 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 0 2 3 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 0 2 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 1 2 3 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 1 2 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 0 3 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 1 3 4 = z / 4 - 1 / 16
        ∧ hingeAreaSqC (hingeEdges32C z) 2 3 4 = z / 4 - 1 / 16) :=
  ⟨fourOne_areaSq_spacelike z, fourOne_areaSq_timelike z,
    threeTwo_areaSq_closed z⟩

/-- THEOREM (B3, kill certificates memorialized): the two product-form
gate FAIL events as one kernel statement: at interior arc parameters the
diagonal-cofactor PRODUCT sits ON the `csqrt` branch cut with the exact
values `-40` (mixed class, `tStarMixed`) and `-48` (upper-pair class,
`t = 2/3` exactly).  The single-sqrt product transcription stays KILLED;
the split-sqrt form is the repaired convention. -/
theorem wick_product_form_kills_memorialized :
    (tStarMixed ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 tStarMixed) 1 1
          * cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 tStarMixed) 4 4
          = -40
      ∧ (-40 : ℂ) ∉ Complex.slitPlane)
      ∧ ((2 / 3 : ℝ) ∈ Set.Ioo (0 : ℝ) 1
      ∧ cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 (2 / 3)) 1 1
          * cmCofactorC (continuationEdgesC CausalPentType.threeTwo 1 1 (2 / 3)) 2 2
          = -48
      ∧ (-48 : ℂ) ∉ Complex.slitPlane) :=
  ⟨product_form_crossing_threeTwo_mixed, product_form_crossing_threeTwo_upper⟩

/-- Documentation theorem (by `rfl` on the hand-set status record): the
action-level continuation flag of the kinematical layer is still OPEN.
This module proves hinge-data continuation and deliberately does NOT
change that status. -/
theorem action_level_still_open :
    causalSimplex4DStatus.action_level_continuation_open = true := rfl

/-! ## Axiom audit

Expected: `[propext, Classical.choice, Quot.sound]`. -/

#print axioms wick_hinge_data_continuation_complete
#print axioms wick_hinge_areaSq_closed_forms_complete
#print axioms wick_product_form_kills_memorialized

end WickHingeDataComplete
end SevenGaps
end Gravity
end IndisputableMonolith

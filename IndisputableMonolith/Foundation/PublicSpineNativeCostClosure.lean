/-
  Foundation/PublicSpineNativeCostClosure.lean

  Round-trip source:
    plans/Delta_JCost_FreeSide_Program_Plan_20260724.html  (rounds 7 and 8)

  ROUNDS 7 AND 8: re-point the public spine.

  `PublicSpine.cost_selection_holds` and `PublicSpine.phi_from_iota_holds` are
  both tagged `traceClosure`, because both are stated on ℝ. The adjacent clause
  in the same certificate (`continuum_is_purchase`) says the completed line is
  not forced. A spine that buys its keystone in a currency the next clause calls
  optional is not a stratification, it is an IOU.

  This module pays the IOU. It cannot live inside `PublicSpine` itself: the
  δ-native cost modules import `PublicSpine` for the `Tagged` wrapper, so the
  deposit has to sit downstream. That is the same shape as
  `PublicSpineLinkingClosure`, which inhabits the D=3 binder from below.

  What lands here:

  * `native_cost_selection_holds` — cost selection at `deltaOnly`, on the
    countable carrier, from the structural ledger of rounds 4 to 6. Its content
    is the full round-6 stratification: uniqueness, the recovery of the round-3
    ledger, derived positivity, an inhabited gauge orbit, and gauge rigidity.
  * `cost_selection_inversion_holds` — the continuum clause, restated as a
    corollary of the native one plus a priced completion step. The arrow between
    the two surfaces now points from free to bought.
  * `native_phi_holds` — three of the four reciprocal-generator facts at
    `deltaOnly`, plus a proof that the fourth (the self-similar scale) is
    genuinely a purchase: no ratio orbit solves `1 + 1/x = x`.
  * `publicSpineCertNative_holds` — the upgraded substrate certificate.

  Nothing upstream is edited and no physics changes. The citation target moves.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCNativeCostContinuumCorollary

namespace IndisputableMonolith
namespace Foundation
namespace PublicSpine

open PrimitiveRecognitionCalculus
open PrimitiveRecognitionCalculus.PRCJCost

/-! ## Round 7: cost selection at the floor

The claim deposited here is the free-side mirror of `CostSelectionPackage`: the
cost is pinned on the δ-native carrier, by a ledger of structural facts (what a
cost IS) rather than a ledger of calibrations (where a cost AGREES with J), with
no continuity, no smoothness, and no completed line anywhere in the hypotheses
or the proof. -/

/-- **δ-native cost selection.** Tagged `deltaOnly`. -/
structure NativeCostSelectionPackage : Prop where
  /-- The headline: the structural ledger forces the canonical cost at every
  point of the countable carrier. -/
  j_unique_native : PRCStructuralNativeCostUniquenessTarget
  /-- And the full round-6 stratification: the ledger recovers the round-3
  calibration ledger, positivity is derived rather than assumed, the surviving
  anchor is an inhabited gauge, and it is the only one. -/
  stratification : StructuralStratificationCertificate

theorem native_cost_selection_holds :
    Tagged StrengthTag.deltaOnly NativeCostSelectionPackage where
  holds :=
    { j_unique_native := PRCStructuralNativeCostUniquenessTarget_proved
      stratification := structuralStratificationCertificate_holds }

/-- **The inversion.** Both surfaces, side by side, with the arrow between them
and the exact price of crossing it. Tagged `traceClosure` because it mentions
the continuum clause; the free half of it is `native_cost_selection_holds`. -/
structure CostSelectionInversion : Prop where
  /-- The free side. -/
  native : NativeCostSelectionPackage
  /-- The continuous theorem, still true, still cited by the physics. -/
  continuum : CostSelectionPackage
  /-- The continuous conclusion, re-derived from the native one plus a completion
  step, with a witness that the step is not redundant. -/
  bridge : PRCJCost.InvertedCostBridge
  /-- And the tags are genuinely ordered: this is a strict overpay, not a
  relabelling. -/
  strictly_stronger : StrengthTag.deltaOnly < StrengthTag.traceClosure

theorem cost_selection_inversion_holds :
    Tagged StrengthTag.traceClosure CostSelectionInversion where
  holds :=
    { native := native_cost_selection_holds.holds
      continuum := cost_selection_holds.holds
      bridge := PRCJCost.invertedCostBridge_holds
      strictly_stronger := StrengthTag.deltaOnly_lt_traceClosure }

/-- Round-7 headline, in one line: the keystone is paid for at the floor, and
what the completed line adds to it is a domain, not an answer. -/
theorem cost_selection_is_free_up_to_a_domain :
    Tagged StrengthTag.deltaOnly NativeCostSelectionPackage ∧
      (∀ (F : ℝ → ℝ) (G : RatioOrbit → RatioOrbit),
        PRCStructuralNativeCostHypotheses G →
          (∀ q : RatioOrbit, 0 < q.toRat →
            F ((q.toRat : ℚ) : ℝ) = (((G q).toRat : ℚ) : ℝ)) →
            ContinuousOn F (Set.Ioi 0) → ∀ x : ℝ, 0 < x → F x = Cost.Jcost x) :=
  ⟨native_cost_selection_holds,
    PRCJCost.invertedCostBridge_holds.continuum_is_a_corollary⟩

/-! ## Round 8: φ, split into the free part and the purchase

`PhiFromIota` bundles `ReciprocalGeneratorCert`, which lives on ℝ and is tagged
`traceClosure` whole. Most of it does not need the line. The involution, the
reciprocal symmetry of the cost, and the characterization of the unit as the
unique zero-cost orbit are all δ-native facts about the carrier, proved in
`PRCNativeCostStructuralLedger`.

The remaining fact is the self-similar scale, and this is where the completion is
actually bought. The δ-native carrier has no solution to `1 + 1/x = x`. That is
not a gap in the derivation, it is the derivation: the fixed point is the first
object in this chain that the countable carrier genuinely cannot hold, so the tag
on it is honest and now has a proof behind it instead of a shrug. -/

/-- **δ-native reciprocal generator.** Tagged `deltaOnly`: every field is a
statement about ratio orbits. -/
structure NativePhiPackage : Prop where
  split : PRCJCost.NativeReciprocalGeneratorSplit

theorem native_phi_holds :
    Tagged StrengthTag.deltaOnly NativePhiPackage where
  holds := { split := PRCJCost.nativeReciprocalGeneratorSplit_holds }

/-- **The φ purchase, priced.** The scale equation has no δ-native solution, so
the step to the completed line is where φ is actually bought. Tagged `deltaOnly`
because the statement quantifies over the carrier only: it is a fact about what
the free side does NOT contain. -/
theorem phi_scale_is_a_purchase :
    Tagged StrengthTag.deltaOnly
      (¬ ∃ q : RatioOrbit, 0 < q.toRat ∧ 1 + (q.toRat)⁻¹ = q.toRat) where
  holds := PRCJCost.no_native_golden_scale

/-- Round-8 headline: the reciprocal generator splits cleanly. Everything it says
about cost is free; exactly one fact, the fixed point, is bought. -/
structure PhiStratification : Prop where
  free_part : NativePhiPackage
  bought_part : ¬ ∃ q : RatioOrbit, 0 < q.toRat ∧ 1 + (q.toRat)⁻¹ = q.toRat
  continuum_part : PhiFromIota
  strictly_stronger : StrengthTag.deltaOnly < StrengthTag.traceClosure

theorem phi_stratification_holds :
    Tagged StrengthTag.traceClosure PhiStratification where
  holds :=
    { free_part := native_phi_holds.holds
      bought_part := PRCJCost.no_native_golden_scale
      continuum_part := phi_from_iota_holds.holds
      strictly_stronger := StrengthTag.deltaOnly_lt_traceClosure }

/-! ## The upgraded substrate certificate -/

/-- The public substrate, with the cost and φ clauses re-pointed. Extends
`PublicSpineCert` rather than replacing it: the continuum deposits stay exactly
where they were, and the physics that cites them is untouched. What changes is
that the spine now also carries the free-side deposit and the priced bridge
between them. -/
structure PublicSpineCertNative : Prop where
  base : PublicSpineCert
  native_cost_selection : Tagged StrengthTag.deltaOnly NativeCostSelectionPackage
  cost_selection_inversion : Tagged StrengthTag.traceClosure CostSelectionInversion
  native_phi : Tagged StrengthTag.deltaOnly NativePhiPackage
  phi_purchase : Tagged StrengthTag.deltaOnly
    (¬ ∃ q : RatioOrbit, 0 < q.toRat ∧ 1 + (q.toRat)⁻¹ = q.toRat)
  phi_stratification : Tagged StrengthTag.traceClosure PhiStratification

theorem publicSpineCertNative_holds : PublicSpineCertNative where
  base := publicSpineCert_holds
  native_cost_selection := native_cost_selection_holds
  cost_selection_inversion := cost_selection_inversion_holds
  native_phi := native_phi_holds
  phi_purchase := phi_scale_is_a_purchase
  phi_stratification := phi_stratification_holds

/-- Preferred citation for the re-pointed substrate. -/
abbrev SubstrateCertNative : Prop := PublicSpineCertNative

theorem substrateCertNative_holds : SubstrateCertNative := publicSpineCertNative_holds

#print axioms native_cost_selection_holds
#print axioms cost_selection_inversion_holds
#print axioms native_phi_holds
#print axioms phi_scale_is_a_purchase
#print axioms publicSpineCertNative_holds

end PublicSpine
end Foundation
end IndisputableMonolith

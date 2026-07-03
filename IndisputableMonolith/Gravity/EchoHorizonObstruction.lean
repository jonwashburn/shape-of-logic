import Mathlib
import IndisputableMonolith.Gravity.BlackHoleEchoesFromBounce

namespace IndisputableMonolith
namespace Gravity
namespace EchoHorizonObstruction

open BlackHoleEchoesFromBounce

/-!
# Echo Horizon Obstruction: Causal Impossibility of Exterior Return from Interior Bounce

## Abstract

This module formalizes the causal obstruction that rejects the bounce-echo mechanism
described in `BlackHoleEchoesFromBounce`. An event horizon is a one-way boundary:
once a signal crosses to the interior, it cannot return to the exterior. The rejected
echo mechanism required all three of:

1. A signal crosses from the exterior to the interior of an event horizon.
2. The signal reflects at a microscopic interior bounce radius strictly inside the horizon.
3. The signal returns to the **same** exterior region.

We encode this as an abstract causal model and prove that any such `ExteriorReturnClaim`
violates horizon causality: the one-way boundary axiom (interior is closed under the
future-directed step) makes the bounce-to-return path causally forbidden.

This is an abstract causal model, not a formalization of full Lorentzian geometry.
The obstruction is purely combinatorial: a set closed under a function cannot reach
its complement via iterated application of that function.

## Connection to `BlackHoleEchoesFromBounce`

The module `BlackHoleEchoesFromBounce` records `bounce_escape_mechanism_rejected := true`
in `blackHoleEchoMechanismStatus`. This module provides the formal causal obstruction
that justifies that rejection: any exterior-return claim with an interior bounce
is causally impossible under the one-way boundary axiom.
-/

/-- Reflexive-transitive closure of a deterministic step function.
    `StepStar step p q` means `q` is reachable from `p` in zero or more
    applications of `step`, defined by its universal property: any predicate
    closed under `step` that holds at `p` also holds at `q`. -/
def StepStar {Point : Type} (step : Point → Point) (p q : Point) : Prop :=
  ∀ P : Point → Prop, (∀ x, P x → P (step x)) → P p → P q

namespace StepStar

/-- Base case: every point reaches itself. -/
lemma base {Point : Type} {step : Point → Point} (p : Point) : StepStar step p p := by
  intros P h hp
  exact hp

/-- Successor case: if `q` is reachable from `p`, then `step q` is also
    reachable from `p`. -/
lemma succ {Point : Type} {step : Point → Point} {p q : Point}
    (hs : StepStar step p q) : StepStar step p (step q) := by
  intros P hstep hp
  exact hstep q (hs P hstep hp)

/-- If a predicate is closed under `step`, it is preserved by `StepStar`:
    any point reachable from a point satisfying `P` also satisfies `P`.
    This is the combinatorial heart of the one-way boundary: a set closed
    under a function cannot reach its complement via iteration. -/
lemma preserves_predicate {Point : Type} {step : Point → Point}
    {P : Point → Prop} (h : ∀ p, P p → P (step p)) :
    ∀ {p q : Point}, StepStar step p q → P p → P q := by
  intros p q hs
  exact hs P h

/-- Transitivity: reachability chains compose. -/
lemma trans {Point : Type} {step : Point → Point} {p q r : Point}
    (hpq : StepStar step p q) (hqr : StepStar step q r) :
    StepStar step p r := by
  intros P h hp
  exact hqr P h (hpq P h hp)

end StepStar

/-- An abstract causal model with a one-way event horizon.

The key axiom is `interior_closed_under_step`: the interior predicate is
closed under the future-directed step. This encodes the event horizon
as a one-way boundary—once inside, always inside. No interior point
can causally reach an exterior point.

This is an abstract model, not a formalization of Lorentzian geometry.
The causal obstruction is purely combinatorial. -/
structure CausalModel where
  /-- Abstract spacetime point type -/
  Point : Type
  /-- Future-directed causal step (deterministic propagation) -/
  step : Point → Point
  /-- Interior of the event horizon -/
  isInterior : Point → Prop
  /-- Exterior of the event horizon -/
  isExterior : Point → Prop
  /-- Strictly interior: microscopic, deep inside the horizon -/
  strictlyInterior : Point → Prop
  /-- Same exterior region (same asymptotic universe) -/
  sameExteriorRegion : Point → Point → Prop
  /-- Strictly interior implies interior -/
  strictlyInterior_implies_interior :
    ∀ p, strictlyInterior p → isInterior p
  /-- **One-way boundary axiom**: interior is closed under the
      future-directed step. Once inside the horizon, always inside. -/
  interior_closed_under_step :
    ∀ p, isInterior p → isInterior (step p)
  /-- Exterior and interior are disjoint (no point is both) -/
  exterior_interior_disjoint :
    ∀ p, isExterior p → ¬ isInterior p

/-- A claim that a signal crosses to the interior, bounces at a microscopic
radius strictly inside the horizon, and returns to the same exterior region.

This captures the three facts the rejected echo mechanism would need
simultaneously:

1. **Crossing**: The signal starts in the exterior and crosses to the interior.
2. **Interior bounce**: The signal reflects at a microscopic radius strictly
   inside the horizon (not at the horizon itself).
3. **Exterior return**: The signal returns to the same exterior region.

Each pair of consecutive points is connected by a causal chain (`StepStar`),
representing future-directed propagation. -/
structure ExteriorReturnClaim (M : CausalModel) where
  /-- Starting point (exterior) -/
  start : M.Point
  /-- Crossing point (where signal enters interior) -/
  crossing : M.Point
  /-- Bounce point (microscopic, strictly inside horizon) -/
  bounce : M.Point
  /-- Return point (back in exterior) -/
  returnPoint : M.Point
  /-- Fact 1a: signal starts in the exterior -/
  start_exterior : M.isExterior start
  /-- Fact 1b: signal crosses to the interior -/
  crossing_interior : M.isInterior crossing
  /-- Fact 2: bounce at microscopic radius strictly inside the horizon -/
  bounce_strictly_inside_horizon : M.strictlyInterior bounce
  /-- Fact 3a: signal returns to the exterior -/
  returnPoint_exterior : M.isExterior returnPoint
  /-- Fact 3b: returns to the **same** exterior region -/
  returnPoint_same_exterior_region : M.sameExteriorRegion start returnPoint
  /-- Causal chain: start → crossing -/
  start_to_crossing : StepStar M.step start crossing
  /-- Causal chain: crossing → bounce -/
  crossing_to_bounce : StepStar M.step crossing bounce
  /-- Causal chain: bounce → return -/
  bounce_to_return : StepStar M.step bounce returnPoint

/-- Predicate: a claim violates horizon causality (its return point is
    both interior and exterior, which is causally impossible under the
    one-way boundary axiom). -/
def ViolatesHorizonCausality {M : CausalModel} (claim : ExteriorReturnClaim M) : Prop :=
  M.isInterior claim.returnPoint ∧ M.isExterior claim.returnPoint

/-- **Main theorem.** Any exterior-return claim with an interior bounce
    (strictly inside the horizon) violates horizon causality: the return
    point must be interior (by the one-way boundary axiom) but is also
    claimed to be exterior (by the return fact), which is impossible.

    The proof uses the one-way boundary axiom: since the bounce point is
    strictly interior (hence interior), and the interior is closed under
    the future-directed step, the return point—reachable from the bounce
    via `StepStar`—must also be interior. But the claim asserts the return
    point is exterior, contradicting the disjointness of interior and
    exterior. -/
theorem bounce_echo_mechanism_violates_horizon_causality
    (M : CausalModel) (claim : ExteriorReturnClaim M) :
    ViolatesHorizonCausality claim := by
  unfold ViolatesHorizonCausality
  refine ⟨?_, claim.returnPoint_exterior⟩
  -- The bounce point is strictly interior, hence interior
  have hbounce_interior : M.isInterior claim.bounce :=
    M.strictlyInterior_implies_interior claim.bounce
      claim.bounce_strictly_inside_horizon
  -- By the one-way boundary, the return point is interior
  -- (StepStar preserves the interior predicate since it is closed under step)
  exact claim.bounce_to_return M.isInterior
    (fun p hp => M.interior_closed_under_step p hp) hbounce_interior

/-- Corollary: an exterior-return claim with interior bounce is causally
    impossible (leads to contradiction). -/
theorem exterior_return_claim_impossible
    (M : CausalModel) (claim : ExteriorReturnClaim M) : False := by
  have h := bounce_echo_mechanism_violates_horizon_causality M claim
  exact M.exterior_interior_disjoint claim.returnPoint h.2 h.1

/-- The obstruction is consistent with the status recorded in
    `BlackHoleEchoesFromBounce`: the bounce escape mechanism is rejected. -/
theorem blackHoleEchoMechanismStatus_records_rejection :
    blackHoleEchoMechanismStatus.bounce_escape_mechanism_rejected = true := by
  rfl

end EchoHorizonObstruction
end Gravity
end IndisputableMonolith
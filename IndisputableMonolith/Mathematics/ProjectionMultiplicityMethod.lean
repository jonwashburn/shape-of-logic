import Mathlib

/-!
# Projection Multiplicity Method

This module records the abstract method exposed by the Erdős unit-distance
miss: a classical extremal problem can be attacked by lifting it to a richer
carrier, producing many hidden carrier events, and projecting those events back
to the visible classical surface.

The point is not to formalize the OpenAI/Sawin proof.  The point is to name the
method so future classical problems are checked for the same failure mode:
visible-dimensional counting can be beaten when a high-rank carrier has many
distinct events that project to the same low-dimensional invariant.
-/

namespace IndisputableMonolith
namespace Mathematics
namespace ProjectionMultiplicityMethod

open Filter
open scoped Topology

universe u v

/-- A classical extremal problem consists of visible objects, a relation whose
instances are counted, and two numerical readouts: visible size and event count. -/
structure ClassicalExtremalProblem where
  Visible : Type u
  relation : Visible → Visible → Prop
  size : Finset Visible → ℝ
  eventCount : Finset (Visible × Visible) → ℝ

/-- A lift puts the visible problem on a richer carrier and projects back. -/
structure LiftData (P : ClassicalExtremalProblem.{u}) where
  Carrier : Type v
  project : Carrier → P.Visible
  carrierRelation : Carrier → Carrier → Prop
  energy : Carrier → ℝ

/-- A finite window in the carrier, together with its projected visible set and
the events certified inside the window. -/
structure FiniteWindow {P : ClassicalExtremalProblem.{u}}
    (L : LiftData.{u, v} P) where
  carrierSet : Finset L.Carrier
  visibleSet : Finset P.Visible
  liftedEvents : Finset (L.Carrier × L.Carrier)
  visibleEvents : Finset (P.Visible × P.Visible)
  projection_covers :
    ∀ x ∈ carrierSet, L.project x ∈ visibleSet
  event_sound :
    ∀ e ∈ liftedEvents,
      L.carrierRelation e.1 e.2 ∧
        P.relation (L.project e.1) (L.project e.2)
  event_projects :
    ∀ e ∈ liftedEvents,
      (L.project e.1, L.project e.2) ∈ visibleEvents

/-- The projected event count beats linear growth by a fixed exponent. -/
def BeatsLinearBy (N E : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ᶠ k in atTop, 0 < N k ∧ Real.rpow (N k) (1 + δ) ≤ E k

/-- A projection-multiplicity certificate is the abstract shape of the
lift-return proof:

1. choose a richer carrier;
2. choose finite windows in that carrier;
3. certify that carrier events project to valid visible events;
4. prove a fixed polynomial gain in the visible event count.
-/
structure ProjectionMultiplicityCertificate where
  P : ClassicalExtremalProblem.{u}
  L : LiftData.{u, v} P
  window : ℕ → FiniteWindow L
  visibleSize : ℕ → ℝ
  eventCount : ℕ → ℝ
  delta : ℝ
  delta_pos : 0 < delta
  size_matches :
    ∀ᶠ k in atTop, visibleSize k = P.size ((window k).visibleSet)
  event_matches :
    ∀ᶠ k in atTop, eventCount k = P.eventCount ((window k).visibleEvents)
  polynomial_gain : BeatsLinearBy visibleSize eventCount delta

/-- The formal output of the method: the lifted carrier gives a visible
polynomial gain. -/
theorem certificate_gives_polynomial_gain
    (C : ProjectionMultiplicityCertificate.{u, v}) :
    ∃ δ : ℝ, 0 < δ ∧ BeatsLinearBy C.visibleSize C.eventCount δ :=
  ⟨C.delta, C.delta_pos, C.polynomial_gain⟩

/-- Diagnostic predicate for the rule we missed.  A problem should be checked
for projection multiplicity when its visible relation can be expressed as the
projection of a carrier relation and the event count is controlled by fiber
multiplicity rather than by visible dimension alone. -/
structure ProjectionMultiplicityCandidate where
  has_hidden_carrier : Prop
  visible_relation_is_projected : Prop
  fibers_can_grow : Prop
  carrier_geometry_stays_controlled : Prop

/-- The candidate has the four tests required before starting a full
projection-multiplicity attack. -/
def ProjectionMultiplicityCandidate.Ready
    (C : ProjectionMultiplicityCandidate) : Prop :=
  C.has_hidden_carrier ∧
    C.visible_relation_is_projected ∧
    C.fibers_can_grow ∧
    C.carrier_geometry_stays_controlled

end ProjectionMultiplicityMethod
end Mathematics
end IndisputableMonolith

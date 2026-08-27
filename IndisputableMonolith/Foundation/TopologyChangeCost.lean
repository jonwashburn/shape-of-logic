import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Cost of topology change

DEP says a posted dual-pair distinction cannot be erased by recognition-free
deformation. The realization layer does not force DEP
(`LinkingNecessity.dep_not_forced_by_realization_layer`). This module supplies
the missing cost-layer model:

* an integer linking charge `lk`
* isotopy events preserve `lk` and cost `0`
* crossing events change `lk` by a nonzero integer and cost `J(φ) > 0`

In this model every erasure of a nonzero charge uses a crossing, so every
erasure has positive J-cost. That is DEP, discharged inside the model.

The event vocabulary is MODEL. The cost consequences are THEOREM.
This does not derive DEP from the D=4 everything-deforms kinematics.

Status: 0 sorry, 0 new axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace TopologyChangeCost

/-- MODEL: the two expressible events. A crossing changes the charge by a
nonzero integer. -/
inductive Event
  | isotopy
  | crossing (δ : {n : ℤ // n ≠ 0})

/-- Cost of an event. Isotopy is free; a crossing pays the unit J-cost of φ. -/
noncomputable def eventCost : Event → ℝ
  | .isotopy => 0
  | .crossing _ => Cost.Jcost Constants.phi

theorem isotopy_cost_zero : eventCost .isotopy = 0 := rfl

theorem crossing_cost_pos (δ : {n : ℤ // n ≠ 0}) :
    0 < eventCost (.crossing δ) :=
  Constants.Jcost_phi_pos

/-- How an event acts on the linking charge. -/
def applyEvent (lk : ℤ) : Event → ℤ
  | .isotopy => lk
  | .crossing δ => lk + δ.val

def applyPath (lk : ℤ) : List Event → ℤ
  | [] => lk
  | e :: rest => applyPath (applyEvent lk e) rest

noncomputable def pathCost : List Event → ℝ
  | [] => 0
  | e :: rest => eventCost e + pathCost rest

theorem applyPath_isotopy_only (lk : ℤ) :
    ∀ es : List Event,
      (∀ e ∈ es, e = .isotopy) → applyPath lk es = lk
  | [], _ => rfl
  | e :: rest, h => by
    have he : e = .isotopy := h e List.mem_cons_self
    have hrest : ∀ e' ∈ rest, e' = .isotopy := fun e' he' =>
      h e' (List.mem_cons_of_mem e he')
    simp [applyPath, applyEvent, he, applyPath_isotopy_only lk rest hrest]

theorem pathCost_nonneg : ∀ es : List Event, 0 ≤ pathCost es
  | [] => le_rfl
  | e :: rest => by
    have hrest := pathCost_nonneg rest
    cases e with
    | isotopy =>
      simp [pathCost, eventCost, hrest]
    | crossing δ =>
      have hpos := crossing_cost_pos δ
      simp [pathCost]
      linarith

theorem pathCost_pos_of_crossing_mem :
    ∀ {es : List Event} {δ : {n : ℤ // n ≠ 0}},
      Event.crossing δ ∈ es → 0 < pathCost es
  | [], _, h => by cases h
  | e :: rest, δ, h => by
    have hrestn := pathCost_nonneg rest
    cases e with
    | isotopy =>
      have hmem : Event.crossing δ ∈ rest := by
        simpa [Event.isotopy] using h
      have hpos := pathCost_pos_of_crossing_mem hmem
      simp [pathCost, eventCost]
      linarith
    | crossing δ' =>
      have hpos := crossing_cost_pos δ'
      simp [pathCost]
      linarith

/-- Erasure: a path of events takes a nonzero charge to zero. -/
def Erases (es : List Event) (lk : ℤ) : Prop :=
  lk ≠ 0 ∧ applyPath lk es = 0

/-- Isotopy alone cannot erase a nonzero charge. -/
theorem erasure_not_isotopy_only {lk : ℤ} {es : List Event}
    (h : Erases es lk) : ¬ ∀ e ∈ es, e = Event.isotopy := by
  intro hall
  have hsame := applyPath_isotopy_only lk es hall
  exact h.1 (hsame.symm.trans h.2)

theorem erasure_exists_crossing {lk : ℤ} {es : List Event}
    (h : Erases es lk) : ∃ δ, Event.crossing δ ∈ es := by
  by_contra hnone
  apply erasure_not_isotopy_only h
  intro e he
  cases e with
  | isotopy => rfl
  | crossing δ => exact (hnone ⟨δ, he⟩).elim

/-- THEOREM: every erasure has positive J-cost. -/
theorem erasure_positive_cost {lk : ℤ} {es : List Event}
    (h : Erases es lk) : 0 < pathCost es := by
  obtain ⟨δ, hδ⟩ := erasure_exists_crossing h
  exact pathCost_pos_of_crossing_mem hδ

/-- DEP in this model: no zero-cost path erases a nonzero charge. -/
def DepInCostModel : Prop :=
  ∀ (lk : ℤ) (es : List Event), Erases es lk → 0 < pathCost es

theorem dep_holds_in_cost_model : DepInCostModel :=
  fun _ _ h => erasure_positive_cost h

/-- Isotopy of a nonzero charge is not an erasure. -/
theorem isotopy_does_not_erase (lk : ℤ) (hlk : lk ≠ 0) :
    ¬ Erases [.isotopy] lk := by
  intro h
  exact hlk (by simpa [Erases, applyPath, applyEvent] using h.2)

/-- A single unit crossing of charge 1 is an erasure and costs J(φ). -/
theorem unit_crossing_erases_one :
    Erases [.crossing ⟨-1, by decide⟩] 1 := by
  constructor
  · decide
  · simp [applyPath, applyEvent]

theorem unit_crossing_costs_Jphi :
    pathCost [.crossing ⟨-1, by decide⟩] = Cost.Jcost Constants.phi := by
  simp [pathCost, eventCost]

end TopologyChangeCost
end Foundation
end IndisputableMonolith

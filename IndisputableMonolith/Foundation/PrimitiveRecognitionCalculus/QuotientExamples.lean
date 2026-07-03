/-
  PrimitiveRecognitionCalculus/QuotientExamples.lean

  Worked quotient examples for the Delta-native analysis plan.

  `QuotientSelection.lean` proves the general theorem: a quotient is physically
  forced exactly by indistinguishability under admitted observables. This file
  records three paper-facing examples:

  * empty-observable phase quotient: if no observable can read phase, all phases
    are identified;
  * separating gauge family: if observables separate states, the quotient is
    trivial;
  * projective-state display: projective equality is just the quotient theorem
    specialized to a state space and observable family.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientSelection

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace QuotientExamples

open QuotientSelection

/-- Toy phase states for the phase-quotient example. -/
abbrev PhaseState := ℤ

/-- If the admitted observable family is empty, every phase state is
indistinguishable and therefore identified by the physical quotient. -/
theorem empty_observable_phase_quotient (x y : PhaseState) :
    proj (X := PhaseState) (C := ℤ) (∅ : Set (PhaseState → ℤ)) x
      = proj (X := PhaseState) (C := ℤ) (∅ : Set (PhaseState → ℤ)) y := by
  apply identified_of_obsEquiv
  intro f hf
  cases hf

/-- If all integer-valued observables are admitted, they separate integer states,
so the quotient is trivial. -/
theorem separating_gauge_family_injective :
    Function.Injective (proj (X := ℤ) (C := ℤ) (Set.univ : Set (ℤ → ℤ))) := by
  apply proj_injective_of_separating
  intro x y h
  exact h (fun z => z) (by simp)

/-- A generic projective-state quotient: two states have the same physical class
exactly when the admitted projective observables cannot distinguish them. -/
theorem projective_state_display {State Obs : Type*} (F : Set (State → Obs)) (x y : State) :
    proj F x = proj F y ↔ ObsEquiv F x y :=
  forced_iff F x y

/-- **Quotient examples headline.** Phase with no readable observable collapses,
a separating gauge family has trivial quotient, and projective-state display is
the quotient theorem specialized to projective observables. -/
theorem quotient_examples_headline :
    (∀ x y : PhaseState,
      proj (X := PhaseState) (C := ℤ) (∅ : Set (PhaseState → ℤ)) x
        = proj (X := PhaseState) (C := ℤ) (∅ : Set (PhaseState → ℤ)) y)
      ∧ Function.Injective (proj (X := ℤ) (C := ℤ) (Set.univ : Set (ℤ → ℤ)))
      ∧ (∀ {State Obs : Type*} (F : Set (State → Obs)) (x y : State),
          proj F x = proj F y ↔ ObsEquiv F x y) :=
  ⟨empty_observable_phase_quotient, separating_gauge_family_injective,
    fun {State} {Obs} F x y => projective_state_display (State := State) (Obs := Obs) F x y⟩

end QuotientExamples
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

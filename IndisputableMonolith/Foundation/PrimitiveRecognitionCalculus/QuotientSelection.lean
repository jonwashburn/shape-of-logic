/-
  PrimitiveRecognitionCalculus/QuotientSelection.lean

  Phase 7 of the Delta-Native Analysis frontier: when is a permitted quotient
  physically forced?

  Pure distinction does not identify distinct orbits; quotients are permitted but
  not native. Physics, by contrast, identifies states under symmetry: gauge
  equivalence, phase identification, charge sectors, projective Hilbert space. The
  bridge is recognition. A quotient becomes forced exactly when no admissible
  observable can distinguish the two states.

  This module formalizes that. Given a family of observables on a state space, two
  states are observationally equivalent when every observable returns the same
  value on them. The physically forced quotient is the quotient by that relation.

  What is proved:

  * `ObsEquiv` is an equivalence relation (`obsSetoid`);
  * `forced_iff` : two states are identified in the quotient iff observationally
                   equivalent (the quotient is exactly the indistinguishability
                   collapse, nothing more, nothing less);
  * `observable_descends` : every admissible observable factors through the
                   quotient (the universal property: the quotient loses no
                   observable information);
  * `proj_injective_of_separating` : a separating observable family forces the
                   trivial quotient (no gauge), so gauge appears precisely when
                   observables fail to separate;
  * `gauge_from_indistinguishability` : the headline. Indistinguishability under
                   all admissible observables is exactly the physically forced
                   identification.

  This is the Delta origin of gauge symmetry: the quotient is not primitive, it is
  forced by the absence of a distinguishing recognition act.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace QuotientSelection

variable {X C : Type*}

/-- Two states are observationally equivalent under the observable family `F`
when every observable in `F` returns the same value on them. -/
def ObsEquiv (F : Set (X → C)) (x y : X) : Prop := ∀ f ∈ F, f x = f y

theorem obsEquiv_refl (F : Set (X → C)) (x : X) : ObsEquiv F x x := fun _ _ => rfl

theorem obsEquiv_symm (F : Set (X → C)) {x y : X} (h : ObsEquiv F x y) : ObsEquiv F y x :=
  fun f hf => (h f hf).symm

theorem obsEquiv_trans (F : Set (X → C)) {x y z : X}
    (hxy : ObsEquiv F x y) (hyz : ObsEquiv F y z) : ObsEquiv F x z :=
  fun f hf => (hxy f hf).trans (hyz f hf)

/-- Observational equivalence packaged as a `Setoid`. -/
def obsSetoid (F : Set (X → C)) : Setoid X where
  r := ObsEquiv F
  iseqv := ⟨obsEquiv_refl F, obsEquiv_symm F, obsEquiv_trans F⟩

/-- The physically forced quotient: the state space modulo indistinguishability. -/
abbrev PhysicalQuotient (F : Set (X → C)) : Type _ := Quotient (obsSetoid F)

/-- The projection sending a state to its physical (gauge) class. -/
def proj (F : Set (X → C)) : X → PhysicalQuotient F := Quotient.mk (obsSetoid F)

/-- **The quotient is exactly the indistinguishability collapse.** Two states map
to the same physical class iff no admissible observable separates them. The
forced quotient adds no identifications beyond indistinguishability and omits
none. -/
theorem forced_iff (F : Set (X → C)) (x y : X) :
    proj F x = proj F y ↔ ObsEquiv F x y :=
  Quotient.eq

/-- **Universal property.** Every admissible observable descends to the quotient:
there is a function on physical classes agreeing with the observable on every
state. The quotient loses no observable information. -/
theorem observable_descends (F : Set (X → C)) (f : X → C) (hf : f ∈ F) :
    ∃ g : PhysicalQuotient F → C, ∀ x, g (proj F x) = f x := by
  refine ⟨Quotient.lift f (fun a b hab => hab f hf), ?_⟩
  intro x
  rfl

/-- **No gauge from a separating family.** If the observable family separates
states, the projection is injective: the forced quotient is trivial. Gauge
identification appears precisely when the observables fail to separate. -/
theorem proj_injective_of_separating (F : Set (X → C))
    (hsep : ∀ x y, ObsEquiv F x y → x = y) : Function.Injective (proj F) := by
  intro x y h
  exact hsep x y ((forced_iff F x y).mp h)

/-- Indistinguishable states are identified in the quotient. -/
theorem identified_of_obsEquiv (F : Set (X → C)) {x y : X} (h : ObsEquiv F x y) :
    proj F x = proj F y :=
  (forced_iff F x y).mpr h

/-- **Phase 7 headline: gauge from indistinguishability.** The physically forced
quotient identifies two states iff no admissible observable distinguishes them
(`forced_iff`); every observable still descends to it (`observable_descends`); and
when observables separate, the quotient collapses to the identity
(`proj_injective_of_separating`). Quotient is not a native operation of
distinction; it is forced exactly by the absence of a distinguishing recognition
act. -/
theorem gauge_from_indistinguishability (F : Set (X → C)) :
    (∀ x y : X, proj F x = proj F y ↔ ObsEquiv F x y)
      ∧ (∀ f ∈ F, ∃ g : PhysicalQuotient F → C, ∀ x, g (proj F x) = f x)
      ∧ ((∀ x y, ObsEquiv F x y → x = y) → Function.Injective (proj F)) :=
  ⟨forced_iff F, fun f hf => observable_descends F f hf, proj_injective_of_separating F⟩

end QuotientSelection
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

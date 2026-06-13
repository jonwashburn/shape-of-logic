import Mathlib

/-!
# Observable Floor Witness

Anil Thapa's T-1 audit identified the physical weakness of using raw
type-theoretic inequality as the primitive floor: gauge-related or
observationally equivalent representatives can be unequal as terms while
physically indistinguishable.

This module separates the two notions. An observable floor is a pair of
states not related by a supplied equivalence or observational relation.
Raw inequality is recovered as the special case where the relation is
equality.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ObservableFloor

/-- A quotient-aware observable floor on a carrier `K`, relative to an
observational relation `r`. It asserts that two states are not identified by
`r`. For gauge theories, `r` should be the physical/gauge equivalence relation,
not raw equality of representatives. -/
def ObservableFloorWitness (K : Type*) (r : K → K → Prop) : Prop :=
  ∃ x y : K, ¬ r x y

/-- Raw bare distinguishability is the equality-relation special case of an
observable floor. -/
theorem observable_iff_bare_for_eq (K : Type*) :
    ObservableFloorWitness K (fun x y => x = y) ↔ ∃ x y : K, x ≠ y :=
  Iff.rfl

/-- Bare inequality does not imply observable distinguishability for an
arbitrary observational relation. Take the indiscrete relation on `ℝ`, where
every pair is observationally equivalent. -/
theorem bare_distinction_does_not_imply_observable_distinction :
    ∃ (K : Type) (r : K → K → Prop),
      (∃ x y : K, x ≠ y) ∧ ¬ ObservableFloorWitness K r := by
  refine ⟨ℝ, (fun _ _ => True), ⟨?_, ?_⟩⟩
  · exact ⟨0, 1, by norm_num⟩
  · rintro ⟨x, y, hxy⟩
    exact hxy trivial

/-- Certificate packaging the quotient-aware floor and the gauge-blindness
counterexample. -/
structure ObservableFloorCert : Prop where
  /-- Equality recovers the legacy bare-distinguishability floor. -/
  equality_case :
    ∀ K : Type*, ObservableFloorWitness K (fun x y => x = y) ↔
      ∃ x y : K, x ≠ y
  /-- Bare inequality alone does not imply observable distinguishability for an
      arbitrary relation. -/
  raw_inequality_not_physical :
    ∃ (K : Type) (r : K → K → Prop),
      (∃ x y : K, x ≠ y) ∧ ¬ ObservableFloorWitness K r

/-- A setoid witness is exactly an observable-floor witness for the setoid's
equivalence relation. This is intentionally a transparent bridge: the physical
content is in choosing the observational/gauge setoid. -/
theorem observableFloorWitness_of_setoid
    {K : Type*} (s : Setoid K) (h : ∃ x y : K, ¬ s.r x y) :
    ObservableFloorWitness K s.r :=
  h

/-- A quotient carrier is non-singleton exactly when the original carrier has
an observable distinction relative to the quotienting setoid.

This is the quotient-aware repair to the raw-inequality objection: physical
distinguishability lives in `Quotient s`, or equivalently in pairs of
representatives not identified by `s.r`. -/
theorem quotient_nontrivial_iff_observableFloor
    {K : Type*} (s : Setoid K) :
    (∃ a b : Quotient s, a ≠ b) ↔ ObservableFloorWitness K s.r := by
  constructor
  · rintro ⟨a, b, hne⟩
    refine Quotient.inductionOn₂ a b ?_ hne
    intro x y hne'
    refine ⟨x, y, ?_⟩
    intro hxy
    exact hne' (Quotient.sound hxy)
  · rintro ⟨x, y, hxy⟩
    refine ⟨Quotient.mk s x, Quotient.mk s y, ?_⟩
    intro hq
    exact hxy (Quotient.exact hq)

/-- The observable-floor certificate is theorem-backed. -/
theorem observableFloorCert : ObservableFloorCert where
  equality_case := observable_iff_bare_for_eq
  raw_inequality_not_physical :=
    bare_distinction_does_not_imply_observable_distinction

/-!
## TODO for Anil's setoid/quotient extension

The intended next layer is the physical quotient theorem:

* backward-compatibility bridge:
  the equality-relation special case recovers the existing
  `AbsoluteFloorClosure.AbsoluteFloorWitness` interface on inhabited
  carriers.
-/

end ObservableFloor
end Foundation
end IndisputableMonolith

import Mathlib

/-!
  SelfBootstrapDistinguishability.lean

  Route A for the absolute-floor program.

  This module records the precise, Lean-checkable part of the
  self-bootstrap argument. It does not pretend to derive an object-level
  non-singleton carrier from nothing. It proves the meta-level facts used
  by the argument: the formal language already distinguishes propositions,
  and the proposition asserting object-level distinguishability is distinct
  from its own denial.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SelfBootstrap

/-- The two-element type carries a definitional distinction. -/
theorem bool_distinguishable : (false : Bool) ≠ true := by
  decide

/-- Any carrier supporting a Boolean predicate with both truth values
inherits an object-level distinction. -/
theorem distinguishability_lifted_from_bool
    {K : Type*} (P : K → Bool)
    (hpos : ∃ x : K, P x = true) (hneg : ∃ x : K, P x = false) :
    ∃ x y : K, x ≠ y := by
  obtain ⟨x, hx⟩ := hpos
  obtain ⟨y, hy⟩ := hneg
  refine ⟨x, y, ?_⟩
  intro hxy
  have hfalse : P x = false := by
    simpa [hxy] using hy
  cases hx.symm.trans hfalse

/-- A proposition is never equal to its negation in classical logic. -/
theorem prop_ne_not (P : Prop) : P ≠ ¬ P := by
  intro h
  by_cases hp : P
  · have hnp : ¬ P := by
      rw [h] at hp
      exact hp
    exact hnp hp
  · have hp' : P := by
      rw [h.symm] at hp
      exact hp
    exact hp hp'

/-- The claim that a carrier admits a non-trivial distinction is itself
distinguishable from the denial of that claim. -/
theorem dist_claim_self_distinguishes (K : Type*) :
    (∃ x y : K, x ≠ y) ≠ (¬ ∃ x y : K, x ≠ y) :=
  prop_ne_not (∃ x y : K, x ≠ y)

/-- The meta-language has at least one non-trivial propositional distinction. -/
theorem meta_language_distinguishes_props : ∃ P Q : Prop, P ≠ Q :=
  ⟨True, False, by
    intro h
    have hf : False := by
      simpa [h] using True.intro
    exact False.elim hf⟩

/-- Route A, honest form: object-level distinguishability is never weaker
than the meta-level fact that the formal language already distinguishes
`Prop` values. The object-level non-singleton condition is still named. -/
theorem distinguishability_forced_given_object_witness
    (K : Type*) (_h_meta_dist : ∃ P Q : Prop, P ≠ Q)
    (h_at_least_two_in_carrier : ∃ x y : K, x ≠ y) :
    ∃ x y : K, x ≠ y :=
  h_at_least_two_in_carrier

/-- Route A certificate: the self-bootstrap route closes at the meta-language
floor, not below it. -/
structure SelfBootstrapCert : Prop where
  meta_distinguishes : ∃ P Q : Prop, P ≠ Q
  claim_not_its_negation : ∀ K : Type*, (∃ x y : K, x ≠ y) ≠ (¬ ∃ x y : K, x ≠ y)

/-- The self-bootstrap certificate is theorem-backed. -/
theorem selfBootstrapCert : SelfBootstrapCert where
  meta_distinguishes := meta_language_distinguishes_props
  claim_not_its_negation := dist_claim_self_distinguishes

end SelfBootstrap
end Foundation
end IndisputableMonolith

import IndisputableMonolith.Foundation.SelfBootstrapDistinguishability

/-!
# Meta-Level Distinction Does Not Force Object-Level Distinction

This module records the sharp limit of the T-1 self-bootstrap route.
The formal language distinguishes propositions, but that meta-level fact
does not force every inhabited object carrier to be non-singleton.

The counterexample is the unit carrier.
-/

namespace IndisputableMonolith
namespace Foundation
namespace MetaDoesNotForceObject

/-- The meta-language has at least one non-trivial propositional distinction. -/
theorem meta_language_distinguishes : ∃ P Q : Prop, P ≠ Q :=
  SelfBootstrap.meta_language_distinguishes_props

/-- Meta-language proposition distinguishability does not force object-level
distinguishability on every inhabited carrier. The unit carrier is inhabited
and has no two distinct points. -/
theorem meta_distinction_does_not_force_object_distinction :
    ¬ (∀ K : Type, Nonempty K → ∃ x y : K, x ≠ y) := by
  intro h
  obtain ⟨x, y, hxy⟩ := h PUnit ⟨PUnit.unit⟩
  cases x
  cases y
  exact hxy rfl

/-- Certificate packaging the honest scope of the self-bootstrap route. -/
structure MetaDoesNotForceObjectCert : Prop where
  /-- The formal meta-language distinguishes propositions. -/
  meta_distinguishes : ∃ P Q : Prop, P ≠ Q
  /-- That meta-level distinction does not imply object-level non-singletonness
      for arbitrary inhabited carriers. -/
  no_uniform_object_distinction :
    ¬ (∀ K : Type, Nonempty K → ∃ x y : K, x ≠ y)

/-- The meta/object separation certificate is theorem-backed. -/
theorem metaDoesNotForceObjectCert : MetaDoesNotForceObjectCert where
  meta_distinguishes := meta_language_distinguishes
  no_uniform_object_distinction :=
    meta_distinction_does_not_force_object_distinction

end MetaDoesNotForceObject
end Foundation
end IndisputableMonolith

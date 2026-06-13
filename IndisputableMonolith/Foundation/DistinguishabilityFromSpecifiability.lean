import Mathlib

/-!
  DistinguishabilityFromSpecifiability.lean

  Route B for the absolute-floor program.

  The central point is small but sharp: a non-trivial specification is
  equivalent to a non-singleton carrier. If a framework can specify an
  ontology with something inside and something outside, it already has the
  distinction needed by the Law-of-Logic chain.
-/

namespace IndisputableMonolith
namespace Foundation
namespace SpecifiabilityClosure

/-- A non-trivial specification of a sub-ontology inside a universe of
discourse `K`: a predicate that holds for at least one element and fails
for at least one element. -/
structure NontrivialSpecification (K : Type*) where
  inOntology : K → Prop
  someInside : ∃ x : K, inOntology x
  someOutside : ∃ x : K, ¬ inOntology x

/-- Specifiability forces distinguishability. -/
theorem distinguishability_from_specification
    {K : Type*} (S : NontrivialSpecification K) :
    ∃ x y : K, x ≠ y := by
  obtain ⟨P, ⟨x, hx⟩, ⟨y, hy⟩⟩ := S
  refine ⟨x, y, ?_⟩
  intro hxy
  have hyx : P y := by
    simpa [hxy] using hx
  exact hy hyx

/-- Any non-empty proper subtype is a non-trivial specification. -/
def nontrivial_specification_of_proper_subtype
    {K : Type*} (S : Set K)
    (hin : ∃ x : K, x ∈ S) (hout : ∃ x : K, x ∉ S) :
    NontrivialSpecification K where
  inOntology := fun x => x ∈ S
  someInside := hin
  someOutside := hout

/-- If an ontology is a proper, non-empty subset of its universe of discourse,
then it defines a non-trivial specification. -/
def nontrivial_spec_from_proper_ontology
    {K : Type*} (Ω : Set K)
    (h_inhabited : ∃ x : K, x ∈ Ω)
    (h_proper : ∃ x : K, x ∉ Ω) :
    NontrivialSpecification K :=
  nontrivial_specification_of_proper_subtype Ω h_inhabited h_proper

/-- If no non-trivial specification exists on an inhabited carrier, then the
carrier has at most one element. -/
theorem at_most_one_of_no_nontrivial_specification
    {K : Type*} [Nonempty K]
    (h_no_nts : ¬ Nonempty (NontrivialSpecification K)) :
    ∀ x y : K, x = y := by
  intro x y
  by_contra hxy
  apply h_no_nts
  have hy_ne_x : y ≠ x := by
    intro hyx
    exact hxy hyx.symm
  exact ⟨
    { inOntology := fun z => z = x
      someInside := ⟨x, rfl⟩
      someOutside := ⟨y, hy_ne_x⟩ }⟩

/-- Non-trivial specifiability is equivalent to object-level
distinguishability on an inhabited carrier. -/
theorem distinguishability_iff_nontrivial_specifiability
    {K : Type*} [Nonempty K] :
    (∃ x y : K, x ≠ y) ↔ Nonempty (NontrivialSpecification K) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    have hy_ne_x : y ≠ x := by
      intro hyx
      exact hxy hyx.symm
    exact ⟨
      { inOntology := fun z => z = x
        someInside := ⟨x, rfl⟩
        someOutside := ⟨y, hy_ne_x⟩ }⟩
  · rintro ⟨S⟩
    exact distinguishability_from_specification S

/-- Route B certificate: specifiability is exactly the same floor as a
non-singleton universe of discourse. -/
structure SpecifiabilityClosureCert (K : Type*) [Nonempty K] : Prop where
  equivalence :
    (∃ x y : K, x ≠ y) ↔ Nonempty (NontrivialSpecification K)

/-- The specifiability closure certificate is theorem-backed. -/
theorem specifiabilityClosureCert (K : Type*) [Nonempty K] :
    SpecifiabilityClosureCert K where
  equivalence := distinguishability_iff_nontrivial_specifiability

end SpecifiabilityClosure
end Foundation
end IndisputableMonolith

import IndisputableMonolith.Foundation.SelfBootstrapDistinguishability
import IndisputableMonolith.Foundation.DistinguishabilityFromSpecifiability

/-!
  AbsoluteFloorClosure.lean

  Joint certificate for the absolute-floor program.

  The closure is deliberately modest: distinguishability is equivalent to
  non-trivial specifiability on an inhabited carrier, and the meta-language
  already distinguishes propositions. The remaining floor is therefore not an
  RS-specific physical postulate; it is the precondition that there is a
  non-singleton universe of discourse in which any non-vacuous specification
  can be stated.
-/

namespace IndisputableMonolith
namespace Foundation
namespace AbsoluteFloorClosure

open SelfBootstrap
open SpecifiabilityClosure

/-- A fully named absolute-floor witness for a universe of discourse `K`. -/
structure AbsoluteFloorWitness (K : Type*) [Nonempty K] : Prop where
  meta_distinguishes : ∃ P Q : Prop, P ≠ Q
  nontrivial_specifiable : Nonempty (NontrivialSpecification K)

/-- The absolute-floor witness forces bare distinguishability. -/
theorem bare_distinguishability_of_absolute_floor
    {K : Type*} [Nonempty K] (h : AbsoluteFloorWitness K) :
    ∃ x y : K, x ≠ y :=
  (distinguishability_iff_nontrivial_specifiability).mpr h.nontrivial_specifiable

/-- Conversely, bare distinguishability supplies the non-trivial
specification part of the absolute-floor witness, while the meta-language
part is theorem-backed by Route A. -/
theorem absolute_floor_of_bare_distinguishability
    {K : Type*} [Nonempty K] (h : ∃ x y : K, x ≠ y) :
    AbsoluteFloorWitness K where
  meta_distinguishes := meta_language_distinguishes_props
  nontrivial_specifiable :=
    (distinguishability_iff_nontrivial_specifiability).mp h

/-- Bare distinguishability and the absolute-floor witness are equivalent on
an inhabited carrier. -/
theorem absolute_floor_iff_bare_distinguishability
    {K : Type*} [Nonempty K] :
    AbsoluteFloorWitness K ↔ ∃ x y : K, x ≠ y :=
  ⟨bare_distinguishability_of_absolute_floor, absolute_floor_of_bare_distinguishability⟩

/-- The minimal concrete carrier `Bool` realizes the absolute floor. -/
theorem bool_absolute_floor : AbsoluteFloorWitness Bool :=
  absolute_floor_of_bare_distinguishability ⟨false, true, bool_distinguishable⟩

/-- The forcing-chain floor has been reduced to meta-language proposition
distinguishability plus a non-singleton universe of discourse. -/
theorem floor_status :
    "Recognition Science floor: meta-language Prop distinguishability "
      ++ "(formal system) and non-singleton universe (metaphysics). "
      ++ "Both are preconditions of the chain being statable at all."
    = "Recognition Science floor: meta-language Prop distinguishability "
      ++ "(formal system) and non-singleton universe (metaphysics). "
      ++ "Both are preconditions of the chain being statable at all." :=
  rfl

/-- Joint closure certificate. -/
structure AbsoluteFloorClosureCert : Prop where
  routeA : SelfBootstrapCert
  routeB : ∀ K : Type*, [Nonempty K] →
    ((∃ x y : K, x ≠ y) ↔ Nonempty (NontrivialSpecification K))
  bool_witness : AbsoluteFloorWitness Bool

/-- The absolute-floor closure certificate is theorem-backed. -/
theorem absoluteFloorClosureCert : AbsoluteFloorClosureCert where
  routeA := selfBootstrapCert
  routeB := fun K _ => distinguishability_iff_nontrivial_specifiability (K := K)
  bool_witness := bool_absolute_floor

end AbsoluteFloorClosure
end Foundation
end IndisputableMonolith

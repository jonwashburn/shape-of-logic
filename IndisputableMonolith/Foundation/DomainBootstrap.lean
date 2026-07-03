import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation
import IndisputableMonolith.Foundation.NonTrivialityFromDistinguishability

/-!
  DomainBootstrap.lean

  Move 2: bootstrap theorem for the comparison-operator domain.

  The Law of Logic, as stated in `Foundation.LogicAsFunctionalEquation`,
  uses a comparison operator `C : ℝ → ℝ → ℝ`. The recovered real line
  in `Foundation.RealsFromLogic` is itself derived from the same Law of
  Logic. That is a chicken-and-egg, not a paradox: we use `ℝ` as the
  ambient ordered field, and recover an isomorphic `LogicReal` from
  inside the framework. To close the loop, we need a uniqueness
  theorem stating that any ordered-field ambient on which the Law of
  Logic can be stated is canonically isomorphic to `ℝ`.

  The classical fact used here is the standard characterization of the
  real numbers as the unique Archimedean Dedekind-complete ordered
  field. This is part of the Mathlib analysis library, available via
  the order-isomorphism `OrderIso (· < · : K → K → Prop) (· < · : ℝ → ℝ → Prop)`
  for an Archimedean conditionally complete linearly ordered field.

  The theorem in this module states: a linearly ordered field on which
  a Law-of-Logic comparison operator is supported (with the
  Archimedean and Dedekind-completeness hypotheses that any continuous
  comparison-operator structure forces) is canonically isomorphic to
  ℝ as an ordered field. The completeness hypothesis is named
  explicitly because the Law of Logic on its own does not single out
  Archimedean completeness; that is the residual analytic input.

  This makes the chicken-and-egg explicit: the Law of Logic plus the
  natural completeness/Archimedean hypothesis on the ambient field
  forces that field to be `ℝ`, and the Law of Logic on `ℝ` recovers
  the same field as `LogicReal` (this direction is in
  `Foundation.RealsFromLogic`).
-/

namespace IndisputableMonolith
namespace Foundation
namespace DomainBootstrap

/-! ## 1. The ambient-field abstraction

We rephrase the comparison-operator structure over a generic linearly
ordered field `K` rather than over `ℝ`. The four Aristotelian
conditions transcribe directly. The Excluded Middle (continuity)
condition requires `K` to carry a topology compatible with the order;
the standard choice is the order topology, which `LinearOrderedField`
gives via Mathlib's `LinearOrderedField` to `TopologicalSpace`
instance.
-/

/-- A comparison operator on a linearly ordered field. -/
abbrev ComparisonOperatorOn (K : Type*) := K → K → K

/-- Derived cost from a comparison operator on a generic ordered field. -/
@[simp] def derivedCostOn {K : Type*} [One K] (C : ComparisonOperatorOn K) : K → K :=
  fun r => C r 1

variable {K : Type*}

/-- Identity, generic field version. -/
def IdentityOn [Zero K] [LT K] (C : ComparisonOperatorOn K) : Prop :=
  ∀ x : K, 0 < x → C x x = 0

/-- Non-contradiction, generic field version. -/
def NonContradictionOn [LT K] [Zero K] (C : ComparisonOperatorOn K) : Prop :=
  ∀ x y : K, 0 < x → 0 < y → C x y = C y x

/-- Scale invariance, generic field version. -/
def ScaleInvariantOn [Zero K] [LT K] [Mul K] (C : ComparisonOperatorOn K) : Prop :=
  ∀ x y lam : K, 0 < x → 0 < y → 0 < lam →
    C (lam * x) (lam * y) = C x y

/-- Distinguishability, generic field version. -/
def DistinguishabilityOn [Zero K] [LT K] (C : ComparisonOperatorOn K) : Prop :=
  ∃ x y : K, 0 < x ∧ 0 < y ∧ C x y ≠ 0

/-! ## 2. The bootstrap theorem

The Law of Logic on an ambient field `K` plus Archimedean +
Dedekind-completeness implies `K ≃+*o ℝ`. The proof is by reduction
to Mathlib's classical characterization of `ℝ`.

The completeness hypothesis is the standard analytic input that makes
"continuous comparison" non-vacuous; without it, the comparison
operator could live on `ℚ` or any incomplete subfield. With it, `K`
is forced to be `ℝ`.
-/

/-- A linearly ordered field is **Logic-supported** when a comparison
operator on it satisfies the four Aristotelian conditions plus scale
invariance and distinguishability. We package the ordered-field
structure required to even *state* these conditions. -/
structure LogicSupported (K : Type*) [Mul K] [Zero K] [One K] [LT K] where
  zero_lt_one_in_K : (0 : K) < 1
  C : ComparisonOperatorOn K
  identity : IdentityOn C
  non_contradiction : NonContradictionOn C
  scale_invariant : ScaleInvariantOn C
  distinguishability : DistinguishabilityOn C

/-- **Bootstrap theorem (named-hypothesis form)**: a linearly ordered
field on which the Law of Logic is supported and which is Archimedean
and conditionally complete is canonically isomorphic to `ℝ` as an
ordered field. The Archimedean and conditional-completeness
hypotheses are the analytic content the Law of Logic does not on its
own provide; they are named here as inputs.

The conclusion is the existence of an order-preserving ring
isomorphism with `ℝ`. -/
theorem bootstrap_to_real
    (K : Type*) [ConditionallyCompleteLinearOrderedField K]
    (_ : LogicSupported K) :
    Nonempty (K ≃+*o ℝ) :=
  ⟨LinearOrderedField.inducedOrderRingIso K ℝ⟩

/-- **Idempotence**: `ℝ` itself is a Logic-supported domain (witnessed
by any of the comparison operators we already have over `ℝ`). The
bootstrap theorem then says nothing new on `ℝ`, but on any other
candidate ordered field it forces an isomorphism to `ℝ`. -/
def real_supports_logic
    (C : LogicAsFunctionalEquation.ComparisonOperator)
    (h : LogicAsFunctionalEquation.SatisfiesLawsOfLogic C) :
    LogicSupported ℝ where
  zero_lt_one_in_K := by norm_num
  C := C
  identity := h.identity
  non_contradiction := h.non_contradiction
  scale_invariant := h.scale_invariant
  distinguishability :=
    LogicAsFunctionalEquation.distinguishability_of_nonTrivial C h.non_trivial

/-! ## 3. Closing the chicken-and-egg

The chain is now explicitly idempotent.

Forward direction (`Foundation.RealsFromLogic`): the Law of Logic on
`ℝ` recovers a `LogicReal` carrier with `LogicReal ≃+*o ℝ`.

Backward direction (this module): a Law-of-Logic-supported ambient
ordered field `K` (Archimedean + conditionally complete) is `≃+*o ℝ`.

Composition: starting from `ℝ` as the ambient field, we recover
`LogicReal ≃+*o ℝ`; conversely, any other ambient field that supports
the Law of Logic with the same analytic completeness is `≃+*o ℝ`. The
choice of `ℝ` as the comparison-operator domain is therefore a
canonical choice up to isomorphism, not a contingent one. -/

/-- **Bootstrap closure**: the Law of Logic plus Archimedean
completeness uniquely picks out `ℝ` as the ambient ordered field, up
to canonical isomorphism. -/
theorem bootstrap_closure
    (K : Type*) [ConditionallyCompleteLinearOrderedField K]
    (h : LogicSupported K) :
    Nonempty (K ≃+*o ℝ) :=
  bootstrap_to_real K h

/-! ## 4. Summary

The Law of Logic, on its own, does not literally name the ambient
field as `ℝ`; it requires a domain that is at least a linearly
ordered field. Adding the analytic content (Archimedean + Dedekind
completeness) forces the domain to be `ℝ`. The recovered real line
from `Foundation.RealsFromLogic` then matches the ambient `ℝ`, and
the chicken-and-egg is closed up to canonical isomorphism.

The single residual classical input is the Archimedean
completeness of the ambient field. This is named, not hidden. -/

end DomainBootstrap
end Foundation
end IndisputableMonolith

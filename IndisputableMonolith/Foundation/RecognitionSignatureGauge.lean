import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientSelection

/-!
# Recognition signatures, gauge quotients, and the one-bit T0 boundary

This module records the Lean-level correction prompted by the T-1/T0 Boolean
shadow audit (June 2026).

A single Boolean distinction is an atomic recognition floor.  It is not a
complete encoding of an arbitrary state space.  The complete observable object,
when it exists, is a family of recognizers/observables and its full signature.

We connect that statement to the existing quotient theorem in
`PrimitiveRecognitionCalculus.QuotientSelection`:

* physical identification is equality of the full recognition signature;
* every admitted observable descends to the quotient;
* a separating family gives an injective projection;
* scalar-cost equality is only a complete gauge invariant under a separate
  completeness hypothesis, not by default;
* one Boolean coordinate is not complete in general (`Bool × Bool`), while the
  two coordinate recognizers do separate.

Status: 0 sorry, 0 project axiom.
-/

namespace IndisputableMonolith
namespace Foundation
namespace RecognitionSignatureGauge

open PrimitiveRecognitionCalculus.QuotientSelection

variable {X C : Type*}

/-! ## Full recognition signatures -/

/-- Equality of the full recognition signature induced by a family of
observables.  This is just observational equivalence under all admitted
observables, named in the T0 language. -/
def SameRecognitionSignature (F : Set (X → C)) (x y : X) : Prop :=
  ObsEquiv F x y

/-- The physical quotient induced by a family of recognizers is exactly equality
of the full recognition signature. -/
theorem signature_forced_quotient_iff (F : Set (X → C)) (x y : X) :
    proj F x = proj F y ↔ SameRecognitionSignature F x y :=
  forced_iff F x y

/-- Every admitted recognition coordinate descends to the signature quotient, so
the quotient loses no observable information from that family. -/
theorem signature_observable_descends (F : Set (X → C)) (f : X → C) (hf : f ∈ F) :
    ∃ g : PhysicalQuotient F → C, ∀ x, g (proj F x) = f x :=
  observable_descends F f hf

/-- If the full recognition signature separates states, the quotient projection
is injective.  This is the precise "complete recognizer family" condition. -/
theorem signature_projection_injective_of_separating (F : Set (X → C))
    (hsep : ∀ x y, SameRecognitionSignature F x y → x = y) :
    Function.Injective (proj F) :=
  proj_injective_of_separating F hsep

/-- Certificate for the correct gauge story: gauge equivalence is equality of
the full admitted recognition signature, not equality under a single Boolean
coordinate. -/
structure RecognitionSignatureGaugeCertificate (F : Set (X → C)) : Prop where
  quotient_exact :
    ∀ x y : X, proj F x = proj F y ↔ SameRecognitionSignature F x y
  observables_descend :
    ∀ f ∈ F, ∃ g : PhysicalQuotient F → C, ∀ x, g (proj F x) = f x
  separating_family_injective :
    (∀ x y, SameRecognitionSignature F x y → x = y) → Function.Injective (proj F)

/-- The full-signature gauge certificate is exactly the existing quotient
selection theorem, re-expressed for T0-family language. -/
theorem recognitionSignatureGaugeCertificate_holds (F : Set (X → C)) :
    RecognitionSignatureGaugeCertificate F where
  quotient_exact := signature_forced_quotient_iff F
  observables_descend := signature_observable_descends F
  separating_family_injective := signature_projection_injective_of_separating F

/-! ## Scalar cost is not automatically a complete invariant -/

/-- A scalar cost is complete for a recognition family only if equality of the
scalar is equivalent to equality of the full recognition signature.  This is a
separate hypothesis, not a consequence of having a scalar cost. -/
def ScalarCostCompleteFor (F : Set (X → C)) (cost : X → ℝ) : Prop :=
  ∀ x y : X, cost x = cost y ↔ SameRecognitionSignature F x y

/-- Under the explicit completeness hypothesis, the scalar-cost kernel matches
the full recognition-signature equivalence.  Without this hypothesis, scalar
cost equality is only a cost observable. -/
theorem scalar_cost_kernel_eq_signature_of_complete
    (F : Set (X → C)) (cost : X → ℝ) (hcomplete : ScalarCostCompleteFor F cost)
    (x y : X) :
    cost x = cost y ↔ SameRecognitionSignature F x y :=
  hcomplete x y

/-! ## One Boolean coordinate is not complete in general -/

/-- A toy two-bit state space for the "one Boolean cannot encode everything"
counterexample. -/
abbrev PairBoolState := Bool × Bool

/-- First coordinate recognizer. -/
def firstBit : PairBoolState → Bool := fun x => x.1

/-- Second coordinate recognizer. -/
def secondBit : PairBoolState → Bool := fun x => x.2

/-- The one-coordinate Boolean family. -/
def firstBitFamily : Set (PairBoolState → Bool) := {f | f = firstBit}

/-- The two-coordinate Boolean family. -/
def pairBitFamily : Set (PairBoolState → Bool) :=
  {f | f = firstBit ∨ f = secondBit}

/-- One Boolean coordinate fails to separate the two states with the same first
bit and different second bit. -/
theorem one_boolean_coordinate_not_complete :
    ∃ x y : PairBoolState,
      x ≠ y ∧ SameRecognitionSignature firstBitFamily x y := by
  refine ⟨(false, false), (false, true), ?_, ?_⟩
  · decide
  · intro f hf
    have hf' : f = firstBit := hf
    rw [hf']
    rfl

/-- The first-bit scalar cost has the same incompleteness: it agrees on two
distinct states. -/
def firstBitScalarCost : PairBoolState → ℝ :=
  fun x => if x.1 then 1 else 0

/-- Scalar cost equality alone is not a complete physical quotient unless a
separate completeness theorem is supplied. -/
theorem first_bit_scalar_cost_not_complete :
    ∃ x y : PairBoolState, x ≠ y ∧ firstBitScalarCost x = firstBitScalarCost y := by
  refine ⟨(false, false), (false, true), ?_, ?_⟩
  · decide
  · rfl

/-- The two coordinate Boolean recognizers separate all states of `Bool × Bool`. -/
theorem pairBitFamily_separating :
    ∀ x y : PairBoolState, SameRecognitionSignature pairBitFamily x y → x = y := by
  intro x y hsig
  cases x with
  | mk x₁ x₂ =>
    cases y with
    | mk y₁ y₂ =>
      have h₁ : x₁ = y₁ := by
        exact hsig firstBit (Or.inl rfl)
      have h₂ : x₂ = y₂ := by
        exact hsig secondBit (Or.inr rfl)
      cases h₁
      cases h₂
      rfl

/-- Therefore the physical quotient by the two-coordinate family is injective:
two Boolean recognizers recover the whole two-bit toy state. -/
theorem pairBitFamily_projection_injective :
    Function.Injective (proj pairBitFamily) :=
  signature_projection_injective_of_separating pairBitFamily pairBitFamily_separating

/-- Compact audit certificate for the T0 Boolean-shadow correction. -/
structure BooleanShadowCompletenessBoundary : Prop where
  /-- One Boolean coordinate is not complete in general. -/
  one_bit_not_complete :
    ∃ x y : PairBoolState,
      x ≠ y ∧ SameRecognitionSignature firstBitFamily x y
  /-- Scalar cost equality is not complete in general. -/
  scalar_cost_not_complete :
    ∃ x y : PairBoolState, x ≠ y ∧ firstBitScalarCost x = firstBitScalarCost y
  /-- A separating family gives an injective quotient projection. -/
  two_bit_signature_injective :
    Function.Injective (proj pairBitFamily)
  /-- Full-signature gauge equivalence is the theorem-grade quotient statement. -/
  full_signature_quotient_exact :
    ∀ {X C : Type*} (F : Set (X → C)) (x y : X),
      proj F x = proj F y ↔ SameRecognitionSignature F x y

/-- The corrected T0 boundary is machine-checkable: one bit is atomic, not
complete; a full signature quotient is theorem-grade; scalar cost completeness
requires an extra completeness hypothesis. -/
theorem booleanShadowCompletenessBoundary_holds :
    BooleanShadowCompletenessBoundary where
  one_bit_not_complete := one_boolean_coordinate_not_complete
  scalar_cost_not_complete := first_bit_scalar_cost_not_complete
  two_bit_signature_injective := pairBitFamily_projection_injective
  full_signature_quotient_exact := fun F x y => signature_forced_quotient_iff F x y

end RecognitionSignatureGauge
end Foundation
end IndisputableMonolith

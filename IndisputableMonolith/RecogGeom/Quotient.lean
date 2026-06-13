import Mathlib
import IndisputableMonolith.RecogGeom.Indistinguishable

/-!
# Recognition Geometry: Recognition Quotient

This module constructs the recognition quotient C_R = C/~ where ~ is the
indistinguishability relation. The quotient collapses configurations that
cannot be told apart by the recognizer.

## Key Construction

Given R : C → E, the recognition quotient is:
  C_R = C / ~

where c₁ ~ c₂ iff R(c₁) = R(c₂).

-/

namespace IndisputableMonolith
namespace RecogGeom

/-! ## Recognition Quotient -/

/-- The recognition quotient C_R = C/~ where ~ is indistinguishability. -/
def RecognitionQuotient {C E : Type*} (r : Recognizer C E) :=
  Quotient (indistinguishableSetoid r)

/-- The canonical projection π : C → C_R -/
def recognitionQuotientMk {C E : Type*} (r : Recognizer C E) (c : C) :
    RecognitionQuotient r :=
  Quotient.mk (indistinguishableSetoid r) c

/-! ## Quotient Properties -/

variable {C E : Type*} (r : Recognizer C E)

/-- Two configurations have the same quotient class iff indistinguishable -/
theorem quotientMk_eq_iff {c₁ c₂ : C} :
    recognitionQuotientMk r c₁ = recognitionQuotientMk r c₂ ↔ c₁ ~[r] c₂ :=
  Quotient.eq (r := indistinguishableSetoid r)

/-- The projection respects the recognizer: same class → same event -/
theorem quotientMk_respects_event {c₁ c₂ : C}
    (h : recognitionQuotientMk r c₁ = recognitionQuotientMk r c₂) :
    r.R c₁ = r.R c₂ :=
  (quotientMk_eq_iff r).mp h

/-- The quotient is nonempty if C is -/
instance [ConfigSpace C] : Nonempty (RecognitionQuotient r) :=
  ⟨recognitionQuotientMk r (ConfigSpace.witness C)⟩

/-! ## Event Map on Quotient -/

/-- The event map factors through the quotient: R = R̄ ∘ π -/
def quotientEventMap : RecognitionQuotient r → E :=
  Quotient.lift r.R (fun _ _ h => h)

/-- The quotient event map makes the diagram commute -/
theorem quotientEventMap_spec (c : C) :
    quotientEventMap r (recognitionQuotientMk r c) = r.R c := rfl

/-- The quotient event map is injective -/
theorem quotientEventMap_injective :
    Function.Injective (quotientEventMap r) := by
  intro q₁ q₂ h
  obtain ⟨c₁, hc₁⟩ := Quotient.exists_rep q₁
  obtain ⟨c₂, hc₂⟩ := Quotient.exists_rep q₂
  simp only [← hc₁, ← hc₂] at h ⊢
  -- h : quotientEventMap r ⟦c₁⟧ = quotientEventMap r ⟦c₂⟧
  -- which means r.R c₁ = r.R c₂
  apply Quotient.sound
  exact h

/-- The quotient is isomorphic to the image of R -/
noncomputable def quotient_equiv_image :
    RecognitionQuotient r ≃ Set.range r.R :=
  Equiv.ofBijective
    (fun q => ⟨quotientEventMap r q,
      Quotient.inductionOn q (fun c => ⟨c, rfl⟩)⟩)
    ⟨fun q₁ q₂ h => by
      simp only [Subtype.mk.injEq] at h
      exact quotientEventMap_injective r h,
     fun ⟨e, c, hc⟩ => ⟨recognitionQuotientMk r c, by simp [quotientEventMap_spec, hc]⟩⟩

/-! ## Lifting Functions to Quotient -/

/-- A function f : C → X descends to the quotient if it respects indistinguishability -/
def liftToQuotient {X : Type*} (f : C → X)
    (hf : ∀ c₁ c₂, Indistinguishable r c₁ c₂ → f c₁ = f c₂) :
    RecognitionQuotient r → X :=
  Quotient.lift f hf

theorem liftToQuotient_spec {X : Type*} (f : C → X)
    (hf : ∀ c₁ c₂, Indistinguishable r c₁ c₂ → f c₁ = f c₂) (c : C) :
    liftToQuotient r f hf (recognitionQuotientMk r c) = f c := rfl

/-! ## Quotient of Local Structure -/

/-- The projection of a set U ⊆ C to the quotient -/
def projectSet (U : Set C) : Set (RecognitionQuotient r) :=
  {q | ∃ c ∈ U, recognitionQuotientMk r c = q}

/-- The induced neighborhood structure on the quotient -/
def quotientNeighborhoods (L : LocalConfigSpace C) :
    RecognitionQuotient r → Set (Set (RecognitionQuotient r)) :=
  fun q => {V | ∃ c : C, recognitionQuotientMk r c = q ∧ ∃ U ∈ L.N c, projectSet r U ⊆ V}

/-! ## Summary Theorem -/

/-- Summary: The recognition quotient captures exactly the observable structure -/
theorem recognition_quotient_summary :
    Function.Surjective (recognitionQuotientMk r) ∧
    Function.Injective (quotientEventMap r) := by
  constructor
  · intro q
    obtain ⟨c, rfl⟩ := Quotient.exists_rep q
    exact ⟨c, rfl⟩
  · exact quotientEventMap_injective r

/-! ## Module Status -/

def quotient_status : String :=
  "✓ RecognitionQuotient defined (C_R = C/~)\n" ++
  "✓ Canonical projection π : C → C_R\n" ++
  "✓ quotientMk_eq_iff: same class ↔ indistinguishable\n" ++
  "✓ quotientEventMap: R̄ : C_R → E\n" ++
  "✓ quotientEventMap_injective: R̄ is injective\n" ++
  "✓ quotient_equiv_image: C_R ≃ Im(R)\n" ++
  "✓ liftToQuotient: lifting functions\n" ++
  "✓ quotientNeighborhoods: induced locality\n" ++
  "\n" ++
  "RECOGNITION QUOTIENT COMPLETE"

#eval quotient_status

end RecogGeom
end IndisputableMonolith

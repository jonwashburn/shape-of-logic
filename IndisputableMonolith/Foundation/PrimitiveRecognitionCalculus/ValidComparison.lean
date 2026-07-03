/-
  PrimitiveRecognitionCalculus/ValidComparison.lean

  Native object -> display object -> observable protocol.

  This module turns the paper doctrine into a reusable formal object. A display
  map is not enough to justify comparison. A valid comparison also needs an
  observable protocol and a bridge showing the displayed value agrees with the
  observable datum.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace ValidComparison

/-- A bridge from a native object `N` to a display object `D` and an observable
object `O`. The commuting law says the display, when observed, agrees with the
native observable protocol. -/
structure Bridge (N D O : Type*) where
  display : N → D
  observeNative : N → O
  observeDisplay : D → O
  commutes : ∀ n : N, observeDisplay (display n) = observeNative n

/-- A display comparison is valid when both displayed values come from native
objects through the same bridge and the displayed observations agree. -/
def IsValidComparison {N D O : Type*} (B : Bridge N D O) (x y : N) : Prop :=
  B.observeDisplay (B.display x) = B.observeDisplay (B.display y)

theorem validComparison_iff_native {N D O : Type*} (B : Bridge N D O) (x y : N) :
    IsValidComparison B x y ↔ B.observeNative x = B.observeNative y := by
  unfold IsValidComparison
  rw [B.commutes x, B.commutes y]

/-- Bridge composition: if a native-to-display bridge and a display-to-display
bridge both commute with the observable protocol, the composite bridge is valid. -/
def compose {N D E O : Type*} (B₁ : Bridge N D O) (B₂ : Bridge D E O) : Bridge N E O where
  display := B₂.display ∘ B₁.display
  observeNative := B₂.observeNative ∘ B₁.display
  observeDisplay := B₂.observeDisplay
  commutes := by
    intro n
    exact B₂.commutes (B₁.display n)

theorem validComparison_compose {N D E O : Type*}
    (B₁ : Bridge N D O) (B₂ : Bridge D E O) (x y : N) :
    IsValidComparison (compose B₁ B₂) x y ↔ B₂.observeNative (B₁.display x) = B₂.observeNative (B₁.display y) :=
  validComparison_iff_native (compose B₁ B₂) x y

/-- **Valid comparison doctrine.** A comparison in a display carrier is legitimate
exactly when it descends to equality of the native observable protocol, and this
legitimacy is stable under composition of display bridges. -/
theorem valid_comparison_doctrine {N D E O : Type*}
    (B₁ : Bridge N D O) (B₂ : Bridge D E O) :
    (∀ x y : N, IsValidComparison B₁ x y ↔ B₁.observeNative x = B₁.observeNative y)
      ∧ (∀ x y : N, IsValidComparison (compose B₁ B₂) x y
          ↔ B₂.observeNative (B₁.display x) = B₂.observeNative (B₁.display y)) :=
  ⟨validComparison_iff_native B₁, validComparison_compose B₁ B₂⟩

end ValidComparison
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

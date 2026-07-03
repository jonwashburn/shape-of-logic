/-
  PrimitiveRecognitionCalculus/ValidComparisonExamples.lean

  Worked valid-comparison examples.

  `ValidComparison.lean` proves the abstract bridge doctrine. This file supplies
  examples the Delta plan asks for: real display, finite probability display, and
  finite Hilbert display.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaReal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.HilbertDisplayCompletion

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace ValidComparisonExamples

/-- Real display bridge: a Delta-real protocol displays to its real value, and
the observable is that same value. -/
noncomputable def realDisplayBridge :
    ValidComparison.Bridge DeltaReal.Protocol ℝ ℝ where
  display := DeltaReal.Protocol.value
  observeNative := DeltaReal.Protocol.value
  observeDisplay := id
  commutes := by intro x; rfl

theorem real_display_valid_iff (x y : DeltaReal.Protocol) :
    ValidComparison.IsValidComparison realDisplayBridge x y ↔ x.value = y.value :=
  ValidComparison.validComparison_iff_native realDisplayBridge x y

/-- Finite probability display bridge: a native finite event displays to its
rational counting probability. -/
noncomputable def probabilityDisplayBridge (N : ℕ) :
    ValidComparison.Bridge (DeltaProbability.Event N) ℚ ℚ where
  display := DeltaProbability.prob
  observeNative := DeltaProbability.prob
  observeDisplay := id
  commutes := by intro E; rfl

theorem probability_display_valid_iff (N : ℕ) (E F : DeltaProbability.Event N) :
    ValidComparison.IsValidComparison (probabilityDisplayBridge N) E F
      ↔ DeltaProbability.prob E = DeltaProbability.prob F :=
  ValidComparison.validComparison_iff_native (probabilityDisplayBridge N) E F

/-- Finite Hilbert display bridge, re-exported at the valid-comparison example
layer. -/
noncomputable def hilbertNormBridge (N : ℕ) :
    ValidComparison.Bridge
      (FRSComplexAmplitude.FRSIAmp N)
      (HilbertDisplayCompletion.FiniteHilbertDisplay N)
      ℝ :=
  HilbertDisplayCompletion.normBridge N

theorem hilbert_display_valid_iff (N : ℕ)
    (ψ φ : FRSComplexAmplitude.FRSIAmp N) :
    ValidComparison.IsValidComparison (hilbertNormBridge N) ψ φ
      ↔ Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight ψ i)
        = Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight φ i) :=
  ValidComparison.validComparison_iff_native (hilbertNormBridge N) ψ φ

/-- **Valid-comparison examples headline.** The doctrine has concrete bridges for
real display, finite probability display, and finite Hilbert display. -/
theorem valid_comparison_examples_headline :
    (∀ x y : DeltaReal.Protocol,
        ValidComparison.IsValidComparison realDisplayBridge x y ↔ x.value = y.value)
      ∧ (∀ (N : ℕ) (E F : DeltaProbability.Event N),
          ValidComparison.IsValidComparison (probabilityDisplayBridge N) E F
            ↔ DeltaProbability.prob E = DeltaProbability.prob F)
      ∧ (∀ (N : ℕ) (ψ φ : FRSComplexAmplitude.FRSIAmp N),
          ValidComparison.IsValidComparison (hilbertNormBridge N) ψ φ
            ↔ Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight ψ i)
              = Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight φ i)) :=
  ⟨real_display_valid_iff, probability_display_valid_iff, hilbert_display_valid_iff⟩

end ValidComparisonExamples
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

/-
  PrimitiveRecognitionCalculus/HilbertDisplayCompletion.lean

  Finite Hilbert space as display completion.

  `FRSComplexAmplitude.lean` closes the native scalar-carrier gap: finite
  amplitudes can live over F_RS[i]. This module names the corresponding finite
  Hilbert display. The display carrier is an ambient complex vector
  `Fin (N+1) → ℂ`; the native carrier is an F_RS[i] amplitude; the bridge
  preserves coordinates, Born weights, normalization, and squared norm.

  Infinite Hilbert space remains a completion/display target. The finite theorem
  here prevents the common mistake: importing ambient ℂ-Hilbert ontology before
  the finite F_RS[i] amplitude has been typed.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FRSComplexAmplitude
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace HilbertDisplayCompletion

/-- The finite Hilbert display carrier: an ambient complex vector on the finite
distinction alternatives. -/
abbrev FiniteHilbertDisplay (N : ℕ) := Fin (N + 1) → ℂ

/-- Display an F_RS[i] amplitude as a finite Hilbert vector. -/
noncomputable def display {N : ℕ} (ψ : FRSComplexAmplitude.FRSIAmp N) : FiniteHilbertDisplay N :=
  FRSComplexAmplitude.displayAmp ψ

/-- Squared norm on the finite Hilbert display. -/
noncomputable def normSq {N : ℕ} (v : FiniteHilbertDisplay N) : ℝ :=
  DeltaAmplitude.complexNormSq v

/-- Born weight on the finite Hilbert display. -/
noncomputable def bornWeight {N : ℕ} (v : FiniteHilbertDisplay N) (i : Fin (N + 1)) : ℝ :=
  DeltaAmplitude.complexBornWeight v i

/-- The Hilbert-display norm equals the native F_RS[i] finite norm. -/
theorem display_normSq_eq {N : ℕ} (ψ : FRSComplexAmplitude.FRSIAmp N) :
    normSq (display ψ)
      = Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight ψ i) :=
  FRSComplexAmplitude.display_normSq_eq ψ

/-- The Hilbert-display Born weight equals the native F_RS[i] Born weight. -/
theorem display_bornWeight_eq {N : ℕ} (ψ : FRSComplexAmplitude.FRSIAmp N) (i : Fin (N + 1)) :
    bornWeight (display ψ) i = FRSComplexAmplitude.bornWeight ψ i :=
  FRSComplexAmplitude.display_bornWeight_eq ψ i

/-- Native F_RS[i] normalization is exactly display-Hilbert normalization. -/
theorem normalized_iff_display {N : ℕ} (ψ : FRSComplexAmplitude.FRSIAmp N) :
    FRSComplexAmplitude.Normalized ψ ↔ normSq (display ψ) = 1 := by
  rw [display_normSq_eq]
  rfl

/-- The valid-comparison bridge from native F_RS[i] amplitudes to the finite
Hilbert display, using squared norm as the observable protocol. -/
noncomputable def normBridge (N : ℕ) :
    ValidComparison.Bridge (FRSComplexAmplitude.FRSIAmp N) (FiniteHilbertDisplay N) ℝ where
  display := display
  observeNative := fun ψ => Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight ψ i)
  observeDisplay := normSq
  commutes := by
    intro ψ
    exact display_normSq_eq ψ

/-- **Finite Hilbert display headline.** Finite Hilbert space is a display of
native F_RS[i] finite amplitudes. The bridge preserves Born weights, squared
norm, and normalization, and comparison by norm is valid through the
native/display/observable bridge. -/
theorem finite_hilbert_display_headline (N : ℕ) :
    (∀ ψ : FRSComplexAmplitude.FRSIAmp N,
        normSq (display ψ)
          = Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight ψ i))
      ∧ (∀ ψ : FRSComplexAmplitude.FRSIAmp N, ∀ i : Fin (N + 1),
          bornWeight (display ψ) i = FRSComplexAmplitude.bornWeight ψ i)
      ∧ (∀ ψ : FRSComplexAmplitude.FRSIAmp N,
          FRSComplexAmplitude.Normalized ψ ↔ normSq (display ψ) = 1)
      ∧ (∀ ψ φ : FRSComplexAmplitude.FRSIAmp N,
          ValidComparison.IsValidComparison (normBridge N) ψ φ
            ↔ Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight ψ i)
              = Finset.univ.sum (fun i : Fin (N + 1) => FRSComplexAmplitude.bornWeight φ i)) :=
  ⟨display_normSq_eq, display_bornWeight_eq, normalized_iff_display,
    fun ψ φ => ValidComparison.validComparison_iff_native (normBridge N) ψ φ⟩

end HilbertDisplayCompletion
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

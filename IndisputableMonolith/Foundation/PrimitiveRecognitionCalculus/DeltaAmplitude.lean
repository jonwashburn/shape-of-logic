/-
  PrimitiveRecognitionCalculus/DeltaAmplitude.lean

  Delta-native amplitude.

  The native object is finite amplitude data, not an infinite-dimensional Hilbert
  space. A finite amplitude vector assigns a real amplitude to each finite
  distinction alternative. The squared norm is a finite sum, and normalization
  gives a finite probability distribution.

  This first pass uses real amplitudes. The complex/Hilbert layer is explicitly a
  display completion to be added on top of this finite carrier.
  The second pass below adds finite complex amplitudes directly; the infinite
  Hilbert space is still only the display completion.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DeltaAmplitude

/-- A finite real amplitude vector on `Fin (N+1)`. -/
abbrev Amp (N : ℕ) := Fin (N + 1) → ℝ

/-- A finite complex amplitude vector on `Fin (N+1)`. -/
abbrev ComplexAmp (N : ℕ) := Fin (N + 1) → ℂ

/-- Squared norm of a finite amplitude vector. -/
noncomputable def normSq {N : ℕ} (ψ : Amp N) : ℝ :=
  Finset.univ.sum fun i : Fin (N + 1) => (ψ i)^2

/-- Born weight of one finite alternative. -/
noncomputable def bornWeight {N : ℕ} (ψ : Amp N) (i : Fin (N + 1)) : ℝ :=
  (ψ i)^2

/-- A finite amplitude is normalized when its squared norm is one. -/
def Normalized {N : ℕ} (ψ : Amp N) : Prop := normSq ψ = 1

theorem bornWeight_nonneg {N : ℕ} (ψ : Amp N) (i : Fin (N + 1)) :
    0 ≤ bornWeight ψ i := by
  unfold bornWeight
  positivity

theorem normSq_nonneg {N : ℕ} (ψ : Amp N) : 0 ≤ normSq ψ := by
  unfold normSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (ψ i))

/-- The Born weights of a normalized finite amplitude sum to one. -/
theorem born_weights_sum_one {N : ℕ} {ψ : Amp N} (hψ : Normalized ψ) :
    Finset.univ.sum (fun i : Fin (N + 1) => bornWeight ψ i) = 1 := by
  simpa [Normalized, normSq, bornWeight] using hψ

/-- A finite linear map preserves norm exactly when it preserves `normSq`. This
is the finite native core of unitary evolution; Hilbert-space unitaries are the
display-completion version. -/
def NormPreserving {N : ℕ} (U : Amp N → Amp N) : Prop :=
  ∀ ψ : Amp N, normSq (U ψ) = normSq ψ

theorem normalized_of_normPreserving {N : ℕ} {U : Amp N → Amp N}
    (hU : NormPreserving U) {ψ : Amp N} (hψ : Normalized ψ) : Normalized (U ψ) := by
  unfold Normalized
  rw [hU ψ, hψ]

/-- **Delta-native amplitude headline.** Finite amplitude data has nonnegative
Born weights; normalized finite amplitudes yield total probability one; and
norm-preserving finite transformations preserve normalization. -/
theorem delta_amplitude_headline (N : ℕ) :
    (∀ ψ : Amp N, ∀ i : Fin (N + 1), 0 ≤ bornWeight ψ i)
      ∧ (∀ ψ : Amp N, Normalized ψ →
          Finset.univ.sum (fun i : Fin (N + 1) => bornWeight ψ i) = 1)
      ∧ (∀ U : Amp N → Amp N, NormPreserving U →
          ∀ ψ : Amp N, Normalized ψ → Normalized (U ψ)) :=
  ⟨bornWeight_nonneg, fun _ hψ => born_weights_sum_one hψ,
    fun _ hU _ hψ => normalized_of_normPreserving hU hψ⟩

/-! ## Complex finite amplitudes -/

/-- Complex Born weight `|z|² = re² + im²` for one finite alternative. -/
noncomputable def complexBornWeight {N : ℕ} (ψ : ComplexAmp N) (i : Fin (N + 1)) : ℝ :=
  (ψ i).re ^ 2 + (ψ i).im ^ 2

/-- Squared norm of a finite complex amplitude vector. -/
noncomputable def complexNormSq {N : ℕ} (ψ : ComplexAmp N) : ℝ :=
  Finset.univ.sum fun i : Fin (N + 1) => complexBornWeight ψ i

/-- A finite complex amplitude is normalized when its squared norm is one. -/
def ComplexNormalized {N : ℕ} (ψ : ComplexAmp N) : Prop := complexNormSq ψ = 1

theorem complexBornWeight_nonneg {N : ℕ} (ψ : ComplexAmp N) (i : Fin (N + 1)) :
    0 ≤ complexBornWeight ψ i := by
  unfold complexBornWeight
  nlinarith [sq_nonneg (ψ i).re, sq_nonneg (ψ i).im]

theorem complexNormSq_nonneg {N : ℕ} (ψ : ComplexAmp N) : 0 ≤ complexNormSq ψ := by
  unfold complexNormSq
  exact Finset.sum_nonneg (fun i _ => complexBornWeight_nonneg ψ i)

theorem complex_born_weights_sum_one {N : ℕ} {ψ : ComplexAmp N} (hψ : ComplexNormalized ψ) :
    Finset.univ.sum (fun i : Fin (N + 1) => complexBornWeight ψ i) = 1 := by
  simpa [ComplexNormalized, complexNormSq] using hψ

/-- Finite complex norm preservation, the native finite version of unitary
evolution. -/
def ComplexNormPreserving {N : ℕ} (U : ComplexAmp N → ComplexAmp N) : Prop :=
  ∀ ψ : ComplexAmp N, complexNormSq (U ψ) = complexNormSq ψ

theorem complex_normalized_of_normPreserving {N : ℕ} {U : ComplexAmp N → ComplexAmp N}
    (hU : ComplexNormPreserving U) {ψ : ComplexAmp N} (hψ : ComplexNormalized ψ) :
    ComplexNormalized (U ψ) := by
  unfold ComplexNormalized
  rw [hU ψ, hψ]

/-- **Complex finite-amplitude headline.** Complex amplitudes already have a
native finite layer: Born weights are nonnegative, normalized finite complex
amplitudes sum to one, and norm-preserving finite complex transformations
preserve normalization. Hilbert space remains the display completion. -/
theorem delta_complex_amplitude_headline (N : ℕ) :
    (∀ ψ : ComplexAmp N, ∀ i : Fin (N + 1), 0 ≤ complexBornWeight ψ i)
      ∧ (∀ ψ : ComplexAmp N, ComplexNormalized ψ →
          Finset.univ.sum (fun i : Fin (N + 1) => complexBornWeight ψ i) = 1)
      ∧ (∀ U : ComplexAmp N → ComplexAmp N, ComplexNormPreserving U →
          ∀ ψ : ComplexAmp N, ComplexNormalized ψ → ComplexNormalized (U ψ)) :=
  ⟨complexBornWeight_nonneg, fun _ hψ => complex_born_weights_sum_one hψ,
    fun _ hU _ hψ => complex_normalized_of_normPreserving hU hψ⟩

end DeltaAmplitude
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

/-
  PrimitiveRecognitionCalculus/FRSComplexAmplitude.lean

  Finite amplitudes over F_RS[i].

  `FRSCarrier.lean` gives the real finite-description carrier F_RS as an explicit
  expression language. `DeltaAmplitude.lean` gives finite real and complex
  amplitudes as native finite vectors, with the ambient complex vector space only
  as display.

  This module closes the next interface gap: a complex amplitude does not need
  the full complex continuum as native scalar carrier. The native scalar is
  F_RS[i], represented by a pair of F_RS expressions `(a,b)` and displayed as
  `a + b i` in ℂ.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FRSCarrier
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaAmplitude

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace FRSComplexAmplitude

/-- A finite-description complex scalar in `F_RS[i]`: real and imaginary parts
are both `F_RS` expressions. -/
structure FRSIExpr where
  re : FRSCarrier.FRSExpr
  im : FRSCarrier.FRSExpr
  deriving DecidableEq, Repr

/-- Display of an `F_RS[i]` expression into the ambient complex field. -/
noncomputable def eval : FRSIExpr → ℂ :=
  fun z => ⟨FRSCarrier.eval z.re, FRSCarrier.eval z.im⟩

/-- Real part of the display is the F_RS real expression value. -/
theorem eval_re (z : FRSIExpr) : (eval z).re = FRSCarrier.eval z.re := rfl

/-- Imaginary part of the display is the F_RS imaginary expression value. -/
theorem eval_im (z : FRSIExpr) : (eval z).im = FRSCarrier.eval z.im := rfl

/-- Every displayed real part remains in the real RS carrier field. -/
theorem eval_re_mem (z : FRSIExpr) : (eval z).re ∈ MinimalField.rsField := by
  simpa [eval] using FRSCarrier.eval_mem z.re

/-- Every displayed imaginary part remains in the real RS carrier field. -/
theorem eval_im_mem (z : FRSIExpr) : (eval z).im ∈ MinimalField.rsField := by
  simpa [eval] using FRSCarrier.eval_mem z.im

/-- Finite amplitude vector over `F_RS[i]`. -/
abbrev FRSIAmp (N : ℕ) := Fin (N + 1) → FRSIExpr

/-- Display an `F_RS[i]` finite amplitude as an ambient finite complex amplitude. -/
noncomputable def displayAmp {N : ℕ} (ψ : FRSIAmp N) : DeltaAmplitude.ComplexAmp N :=
  fun i => eval (ψ i)

/-- Native Born weight computed from the two F_RS components. -/
noncomputable def bornWeight {N : ℕ} (ψ : FRSIAmp N) (i : Fin (N + 1)) : ℝ :=
  FRSCarrier.eval (ψ i).re ^ 2 + FRSCarrier.eval (ψ i).im ^ 2

/-- The displayed complex Born weight agrees with the native F_RS[i] formula. -/
theorem display_bornWeight_eq {N : ℕ} (ψ : FRSIAmp N) (i : Fin (N + 1)) :
    DeltaAmplitude.complexBornWeight (displayAmp ψ) i = bornWeight ψ i := by
  rfl

/-- The displayed complex norm agrees with the native finite F_RS[i] norm formula. -/
theorem display_normSq_eq {N : ℕ} (ψ : FRSIAmp N) :
    DeltaAmplitude.complexNormSq (displayAmp ψ)
      = Finset.univ.sum (fun i : Fin (N + 1) => bornWeight ψ i) := by
  rfl

theorem bornWeight_nonneg {N : ℕ} (ψ : FRSIAmp N) (i : Fin (N + 1)) :
    0 ≤ bornWeight ψ i := by
  unfold bornWeight
  nlinarith [sq_nonneg (FRSCarrier.eval (ψ i).re), sq_nonneg (FRSCarrier.eval (ψ i).im)]

/-- Normalization over `F_RS[i]` is exactly normalization of the ambient complex
display. -/
def Normalized {N : ℕ} (ψ : FRSIAmp N) : Prop :=
  Finset.univ.sum (fun i : Fin (N + 1) => bornWeight ψ i) = 1

theorem normalized_iff_display {N : ℕ} (ψ : FRSIAmp N) :
    Normalized ψ ↔ DeltaAmplitude.ComplexNormalized (displayAmp ψ) := by
  unfold Normalized DeltaAmplitude.ComplexNormalized
  rw [display_normSq_eq]

/-- **F_RS[i] finite amplitude headline.** Finite complex amplitudes can be
carried by the finite-description scalar carrier `F_RS[i]`; ambient ℂ is only the
display. The display preserves real/imaginary carrier membership, Born weights,
and normalization. -/
theorem frsi_amplitude_headline (N : ℕ) :
    (∀ ψ : FRSIAmp N, ∀ i : Fin (N + 1), 0 ≤ bornWeight ψ i)
      ∧ (∀ ψ : FRSIAmp N, DeltaAmplitude.complexNormSq (displayAmp ψ)
          = Finset.univ.sum (fun i : Fin (N + 1) => bornWeight ψ i))
      ∧ (∀ ψ : FRSIAmp N, Normalized ψ ↔ DeltaAmplitude.ComplexNormalized (displayAmp ψ))
      ∧ (∀ z : FRSIExpr, (eval z).re ∈ MinimalField.rsField ∧ (eval z).im ∈ MinimalField.rsField) :=
  ⟨bornWeight_nonneg, display_normSq_eq, normalized_iff_display,
    fun z => ⟨eval_re_mem z, eval_im_mem z⟩⟩

end FRSComplexAmplitude
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

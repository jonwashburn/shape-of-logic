import Mathlib
import IndisputableMonolith.NumberTheory.ZeroLocationCost

/-!
# Completed Xi Symmetry

This module records the minimal functional-equation symmetry surface needed for
Vector C.

It is deliberately small and honest: at this stage we only encode the completed
zeta symmetries that give **pairing data** on zeros. This yields reflection and
conjugation invariants for `zeroDeviation` / `zeroDefect`, but not yet any
d'Alembert-style composition law.
-/

namespace IndisputableMonolith
namespace NumberTheory

open scoped ComplexConjugate

noncomputable section

/-- Minimal completed-ξ symmetry data for Vector C.

`reflection` is the completed functional equation, and `conjugation` is the
standard reality symmetry. Any stronger zero-location constraint must be added
on top of this surface; it is not present here by default. -/
structure CompletedXiSurface where
  xi : ℂ → ℂ
  reflection : ∀ s : ℂ, xi (1 - s) = xi s
  conjugation : ∀ s : ℂ, xi (conj s) = conj (xi s)

/-- The zero set of the completed-ξ surface. -/
def XiZeroSet (Ξ : CompletedXiSurface) : Set ℂ :=
  { s : ℂ | Ξ.xi s = 0 }

/-- The set of zero deviations realized by zeros of a completed-ξ surface. -/
def zeroDeviationSet (Ξ : CompletedXiSurface) : Set ℝ :=
  { t : ℝ | ∃ s : ℂ, Ξ.xi s = 0 ∧ zeroDeviation s = t }

/-- The set of zero defects realized by zeros of a completed-ξ surface. -/
def zeroDefectSet (Ξ : CompletedXiSurface) : Set ℝ :=
  { d : ℝ | ∃ s : ℂ, Ξ.xi s = 0 ∧ zeroDefect s = d }

/-- Functional-equation invariance of the completed-ξ value. -/
theorem xi_reflection_invariant (Ξ : CompletedXiSurface) (s : ℂ) :
    Ξ.xi (functionalReflection s) = Ξ.xi s := by
  simpa [functionalReflection] using Ξ.reflection s

/-- Conjugation symmetry of the completed-ξ value. -/
theorem xi_conjugation_invariant (Ξ : CompletedXiSurface) (s : ℂ) :
    Ξ.xi (conj s) = conj (Ξ.xi s) :=
  Ξ.conjugation s

/-- Zeros come in reflection pairs under the functional equation. -/
theorem zero_pairing_under_reflection (Ξ : CompletedXiSurface) {s : ℂ}
    (hs : Ξ.xi s = 0) :
    Ξ.xi (functionalReflection s) = 0 := by
  simpa [functionalReflection, hs] using Ξ.reflection s

/-- Zeros come in conjugate pairs under reality symmetry. -/
theorem zero_pairing_under_conjugation (Ξ : CompletedXiSurface) {s : ℂ}
    (hs : Ξ.xi s = 0) :
    Ξ.xi (conj s) = 0 := by
  rw [Ξ.conjugation, hs]
  simp

/-- Zeros are stable under reflection composed with conjugation. -/
theorem zero_pairing_under_critical_reflection (Ξ : CompletedXiSurface) {s : ℂ}
    (hs : Ξ.xi s = 0) :
    Ξ.xi (criticalReflection s) = 0 := by
  have hconj : Ξ.xi (conj s) = 0 :=
    zero_pairing_under_conjugation Ξ hs
  simpa [criticalReflection, functionalReflection] using
    zero_pairing_under_reflection Ξ hconj

/-- Reflection and conjugation give the exact zero-location invariants currently
available from the completed-ξ surface. -/
theorem functionalEquation_gives_pairing_invariants
    (Ξ : CompletedXiSurface) {s : ℂ} (hs : Ξ.xi s = 0) :
    Ξ.xi (functionalReflection s) = 0 ∧
      Ξ.xi (conj s) = 0 ∧
      Ξ.xi (criticalReflection s) = 0 ∧
      zeroDeviation (functionalReflection s) = -zeroDeviation s ∧
      zeroDeviation (conj s) = zeroDeviation s ∧
      zeroDefect (functionalReflection s) = zeroDefect s ∧
      zeroDefect (conj s) = zeroDefect s ∧
      zeroDefect (criticalReflection s) = zeroDefect s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact zero_pairing_under_reflection Ξ hs
  · exact zero_pairing_under_conjugation Ξ hs
  · exact zero_pairing_under_critical_reflection Ξ hs
  · exact zeroDeviation_functionalReflection s
  · exact zeroDeviation_conj s
  · exact zeroDefect_invariant_under_functional_reflection s
  · exact zeroDefect_invariant_under_conjugation s
  · exact zeroDefect_invariant_under_reflection s

/-- The functional equation makes the zero-deviation set symmetric under
negation. This is the strongest zero-location consequence currently available
from the minimal completed-ξ surface. -/
theorem zeroDeviationSet_neg_closed (Ξ : CompletedXiSurface) {t : ℝ}
    (ht : t ∈ zeroDeviationSet Ξ) :
    -t ∈ zeroDeviationSet Ξ := by
  rcases ht with ⟨s, hs, rfl⟩
  refine ⟨functionalReflection s, zero_pairing_under_reflection Ξ hs, ?_⟩
  simp

/-- The functional equation preserves the realized zero-defect set. -/
theorem zeroDefectSet_reflection_invariant (Ξ : CompletedXiSurface) {d : ℝ}
    (hd : d ∈ zeroDefectSet Ξ) :
    d ∈ zeroDefectSet Ξ := by
  rcases hd with ⟨s, hs, rfl⟩
  exact ⟨functionalReflection s, zero_pairing_under_reflection Ξ hs,
    zeroDefect_invariant_under_functional_reflection s⟩

end

end NumberTheory
end IndisputableMonolith

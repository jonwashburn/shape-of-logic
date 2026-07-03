import Mathlib
import IndisputableMonolith.NumberTheory.CompletedXiSymmetry
import IndisputableMonolith.NumberTheory.ZeroDoublingLaw
import IndisputableMonolith.NumberTheory.ZeroCompositionInterface

/-!
# Vector C Symmetry-Only No-Go

This module formalizes the main stage gate for Vector C:

functional-equation reflection symmetry plus conjugation symmetry give
pairing data on zeros, but do not by themselves force the critical line.

We certify this with an explicit toy completed-ξ surface whose zeros occur on
the off-line pair `Re(s) = 1/4, 3/4`.
-/

namespace IndisputableMonolith
namespace NumberTheory

open scoped ComplexConjugate

noncomputable section

/-- A toy completed-ξ-style function depending only on the real part.

Its zero set is exactly the union of the two vertical lines `Re(s) = 1/4` and
`Re(s) = 3/4`, so it satisfies reflection and conjugation symmetry while still
admitting off-critical-line zeros. -/
def toyXi (s : ℂ) : ℂ :=
  Complex.ofReal (((s.re - 3 / 4) ^ 2) * ((s.re - 1 / 4) ^ 2))

theorem toyXi_reflection (s : ℂ) :
    toyXi (functionalReflection s) = toyXi s := by
  simp [toyXi, functionalReflection]
  ring

theorem toyXi_conjugation (s : ℂ) :
    toyXi (conj s) = conj (toyXi s) := by
  unfold toyXi
  rw [Complex.conj_ofReal]
  have hre : (conj s).re = s.re := by simp
  rw [hre]

/-- A concrete symmetry surface showing that FE-style pairing data alone does
not force critical-line support. -/
def toyCompletedXiSurface : CompletedXiSurface where
  xi := toyXi
  reflection := toyXi_reflection
  conjugation := toyXi_conjugation

/-- The toy surface has a zero at `s = 3/4`. -/
theorem toyCompletedXiSurface_has_off_critical_zero :
    toyCompletedXiSurface.xi (3 / 4 : ℂ) = 0 ∧
      ¬ OnCriticalLine (3 / 4 : ℂ) := by
  constructor
  · norm_num [toyCompletedXiSurface, toyXi]
  · norm_num [OnCriticalLine]

/-- Reflection/conjugation symmetry of the completed-ξ surface alone is
insufficient to force the critical line. -/
theorem completedXiSurface_symmetry_only_no_go :
    ¬ (∀ Ξ : CompletedXiSurface, ∀ s : ℂ, Ξ.xi s = 0 → OnCriticalLine s) := by
  intro h
  obtain ⟨hzero, hline⟩ := toyCompletedXiSurface_has_off_critical_zero
  exact hline (h toyCompletedXiSurface (3 / 4 : ℂ) hzero)

/-- The negation-closed deviation-set property obtained from the functional
equation does not force `0` to be the only realized deviation. -/
theorem zeroDeviationSet_neg_closed_not_enough :
    ∃ Ξ : CompletedXiSurface,
      (1 / 2 : ℝ) ∈ zeroDeviationSet Ξ ∧
      (-1 / 2 : ℝ) ∈ zeroDeviationSet Ξ ∧
      0 ∉ zeroDeviationSet Ξ := by
  refine ⟨toyCompletedXiSurface, ?_, ?_, ?_⟩
  · refine ⟨(3 / 4 : ℂ), ?_, ?_⟩
    · exact toyCompletedXiSurface_has_off_critical_zero.1
    · norm_num [zeroDeviation]
  · have hhalf : (1 / 2 : ℝ) ∈ zeroDeviationSet toyCompletedXiSurface := by
      refine ⟨(3 / 4 : ℂ), ?_, ?_⟩
      · exact toyCompletedXiSurface_has_off_critical_zero.1
      · norm_num [zeroDeviation]
    have hneg : (-(1 / 2 : ℝ)) ∈ zeroDeviationSet toyCompletedXiSurface :=
      zeroDeviationSet_neg_closed toyCompletedXiSurface hhalf
    norm_num at hneg ⊢
    exact hneg
  · intro hzero
    rcases hzero with ⟨s, hs, hdev⟩
    have hline : OnCriticalLine s :=
      (zeroDeviation_eq_zero_iff_on_critical_line s).mp hdev
    have hvalue :
        toyCompletedXiSurface.xi s =
          (((1 / 2 - 3 / 4) ^ 2 * (1 / 2 - 1 / 4) ^ 2 : ℝ) : ℂ) := by
      simp [toyCompletedXiSurface, toyXi, show s.re = 1 / 2 by exact hline]
    have hnonzero :
        ((((1 / 2 - 3 / 4) ^ 2 * (1 / 2 - 1 / 4) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
      norm_num
    have hxine : toyCompletedXiSurface.xi s ≠ 0 := by
      simpa [hvalue] using hnonzero
    exact hxine hs

/-- The strongest concrete Vector C data currently available from pure
completed-ξ symmetry plus the FE/RCL doubling law. -/
structure PureVectorCDoublingData (Ξ : CompletedXiSurface) (ρ : ℂ) : Prop where
  zero : Ξ.xi ρ = 0
  reflection_zero : Ξ.xi (functionalReflection ρ) = 0
  conjugation_zero : Ξ.xi (conj ρ) = 0
  critical_reflection_zero : Ξ.xi (criticalReflection ρ) = 0
  doubled_recurrence :
    doubledZeroDefect ρ = 2 * (zeroDefect ρ) ^ 2 + 4 * zeroDefect ρ

/-- Any actual completed-ξ zero carries the current pure Vector C package:
pairing invariants plus the FE/RCL doubling recurrence. -/
theorem pureVectorCDoublingData_of_zero (Ξ : CompletedXiSurface) {ρ : ℂ}
    (hρ : Ξ.xi ρ = 0) :
    PureVectorCDoublingData Ξ ρ := by
  refine ⟨hρ, ?_, ?_, ?_, doubledZeroDefect_recurrence ρ⟩
  · exact zero_pairing_under_reflection Ξ hρ
  · exact zero_pairing_under_conjugation Ξ hρ
  · exact zero_pairing_under_critical_reflection Ξ hρ

/-- The current pure Vector C package is realized by an off-critical toy zero. -/
theorem pureVectorCDoublingData_offline_example :
    ∃ Ξ : CompletedXiSurface, ∃ ρ : ℂ,
      PureVectorCDoublingData Ξ ρ ∧ ¬ OnCriticalLine ρ := by
  refine ⟨toyCompletedXiSurface, (3 / 4 : ℂ), ?_, ?_⟩
  · exact pureVectorCDoublingData_of_zero toyCompletedXiSurface
      toyCompletedXiSurface_has_off_critical_zero.1
  · exact toyCompletedXiSurface_has_off_critical_zero.2

/-- Even after adding the current FE/RCL doubling law, pure completed-ξ
symmetry data still cannot force a `ZeroCompositionWitness`.

Therefore any successful upgrade from honest zeta-derived phase data to
`ZeroCompositionWitness` must use genuinely extra analytic input not present in
the pure FE package; in this repository the natural candidates live on the
Euler/Hadamard side (`QuantitativeLocalFactorization`,
`phaseIncrementEpsilonBound`, perturbation/budget control). -/
theorem pureVectorCDoublingData_requires_extra_input :
    ¬ (∀ (Ξ : CompletedXiSurface) (ρ : ℂ),
        PureVectorCDoublingData Ξ ρ → Nonempty (ZeroCompositionWitness ρ)) := by
  intro h
  obtain ⟨Ξ, ρ, hpure, hline⟩ := pureVectorCDoublingData_offline_example
  rcases h Ξ ρ hpure with ⟨w⟩
  exact hline (zeroCompositionWitness_forces_on_critical_line w)

/-- In particular, pure FE symmetry plus the current doubling law do not by
themselves force the critical line. -/
theorem pureVectorCDoublingData_not_enough_for_critical_line :
    ¬ (∀ (Ξ : CompletedXiSurface) (ρ : ℂ),
        PureVectorCDoublingData Ξ ρ → OnCriticalLine ρ) := by
  intro h
  obtain ⟨Ξ, ρ, hpure, hline⟩ := pureVectorCDoublingData_offline_example
  exact hline (h Ξ ρ hpure)

end

end NumberTheory
end IndisputableMonolith

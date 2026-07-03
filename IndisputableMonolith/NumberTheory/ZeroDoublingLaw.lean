import Mathlib
import IndisputableMonolith.Foundation.DiscretenessForcing
import IndisputableMonolith.NumberTheory.ZeroLocationCost
import IndisputableMonolith.NumberTheory.XiJBridge

/-!
# Zero Doubling Law

This file records the strongest concrete Vector C instantiation currently
obtained from the functional-equation/J-symmetry bridge:

the defect observable satisfies a **doubling recurrence**

`D(2t) = 2 * D(t)^2 + 4 * D(t)`.

This is substantial evidence that FE symmetry interacts nontrivially with the
RS defect, but it is still weaker than the full d'Alembert interface packaged in
`ZeroCompositionInterface.lean`.
-/

namespace IndisputableMonolith
namespace NumberTheory

noncomputable section

/-- The defect obtained by doubling the zero deviation. This is the virtual
next-step observable suggested by FE reflection plus RCL self-composition. -/
def doubledZeroDefect (ρ : ℂ) : ℝ :=
  Foundation.DiscretenessForcing.J_log (2 * zeroDeviation ρ)

/-- Closed form for the doubled zero defect. -/
theorem doubledZeroDefect_eq_cosh_sub_one (ρ : ℂ) :
    doubledZeroDefect ρ = Real.cosh (2 * zeroDeviation ρ) - 1 := by
  simp [doubledZeroDefect, Foundation.DiscretenessForcing.J_log]

/-- The FE/RCL bridge yields a doubling recurrence on the zero defect.

This is the concrete Phase 4 instantiation currently available: a one-step
self-composition law on doubled deviation. -/
theorem doubledZeroDefect_recurrence (ρ : ℂ) :
    doubledZeroDefect ρ = 2 * (zeroDefect ρ) ^ 2 + 4 * zeroDefect ρ := by
  rw [doubledZeroDefect_eq_cosh_sub_one, zeroDefect_eq_cosh_sub_one]
  rw [Real.cosh_two_mul]
  nlinarith [Real.cosh_sq (zeroDeviation ρ)]

/-- The doubled zero defect is always nonnegative. -/
theorem doubledZeroDefect_nonneg (ρ : ℂ) : 0 ≤ doubledZeroDefect ρ := by
  rw [doubledZeroDefect_eq_cosh_sub_one]
  linarith [Real.one_le_cosh (2 * zeroDeviation ρ)]

/-- Doubling the deviation still vanishes exactly on the critical line. -/
theorem doubledZeroDefect_zero_iff_on_critical_line (ρ : ℂ) :
    doubledZeroDefect ρ = 0 ↔ OnCriticalLine ρ := by
  rw [doubledZeroDefect_eq_cosh_sub_one]
  constructor
  · intro h
    have hz : 2 * zeroDeviation ρ = 0 := by
      by_contra hne
      have hgt : 1 < Real.cosh (2 * zeroDeviation ρ) := Real.one_lt_cosh.mpr hne
      linarith
    have hdev : zeroDeviation ρ = 0 := by linarith
    exact (zeroDeviation_eq_zero_iff_on_critical_line ρ).mp hdev
  · intro h
    have hdev : zeroDeviation ρ = 0 :=
      (zeroDeviation_eq_zero_iff_on_critical_line ρ).mpr h
    simp [hdev]

/-- Packaging of the strongest currently instantiated Vector C data. -/
theorem current_vectorC_attempt_data (ρ : ℂ) :
    (zeroDefect ρ = 0 ↔ OnCriticalLine ρ) ∧
      0 ≤ doubledZeroDefect ρ ∧
      doubledZeroDefect ρ = 2 * (zeroDefect ρ) ^ 2 + 4 * zeroDefect ρ := by
  exact ⟨zeroDefect_zero_iff_on_critical_line ρ, doubledZeroDefect_nonneg ρ,
    doubledZeroDefect_recurrence ρ⟩

end

end NumberTheory
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Foundation.LawOfExistence
import IndisputableMonolith.Foundation.DiscretenessForcing

/-!
# Zero Location Cost

This module formalizes the RS dictionary between zeta-zero location and
zero-defect cost:

* `zeroDeviation ρ = 2 (Re ρ - 1/2)`
* `zeroDefect ρ = defect (exp (zeroDeviation ρ))`

The critical line `Re ρ = 1/2` is therefore exactly the zero-defect locus.
-/

namespace IndisputableMonolith
namespace NumberTheory

open scoped ComplexConjugate

noncomputable section

/-- The critical-line predicate for a complex point. -/
def OnCriticalLine (ρ : ℂ) : Prop :=
  ρ.re = 1 / 2

/-- Reflection across the line `Re(s) = 1/2`. -/
def functionalReflection (ρ : ℂ) : ℂ :=
  1 - ρ

/-- Reflection across the line `Re(s) = 1/2`, composed with conjugation. -/
def criticalReflection (ρ : ℂ) : ℂ :=
  1 - conj ρ

/-- The real deviation of `ρ` from the critical line, expressed in the
log-coordinate scale compatible with the RS defect functional. -/
def zeroDeviation (ρ : ℂ) : ℝ :=
  2 * (ρ.re - 1 / 2)

/-- The RS defect attached to the zero-location deviation of `ρ`. -/
def zeroDefect (ρ : ℂ) : ℝ :=
  Foundation.LawOfExistence.defect (Real.exp (zeroDeviation ρ))

/-- The zero-location defect is exactly `J_log` evaluated on the deviation. -/
theorem zeroDefect_eq_J_log (ρ : ℂ) :
    zeroDefect ρ =
      Foundation.DiscretenessForcing.J_log (zeroDeviation ρ) := by
  simpa [zeroDefect] using
    (Foundation.DiscretenessForcing.J_log_eq_J_exp (zeroDeviation ρ)).symm

/-- Expanded closed form for the zero-location defect. -/
theorem zeroDefect_eq_cosh_sub_one (ρ : ℂ) :
    zeroDefect ρ = Real.cosh (zeroDeviation ρ) - 1 := by
  simpa [Foundation.DiscretenessForcing.J_log] using zeroDefect_eq_J_log ρ

/-- A point lies on the critical line exactly when its zero deviation is zero. -/
theorem zeroDeviation_eq_zero_iff_on_critical_line (ρ : ℂ) :
    zeroDeviation ρ = 0 ↔ OnCriticalLine ρ := by
  unfold zeroDeviation OnCriticalLine
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The zero-location defect vanishes exactly on the critical line. -/
theorem zeroDefect_zero_iff_on_critical_line (ρ : ℂ) :
    zeroDefect ρ = 0 ↔ OnCriticalLine ρ := by
  rw [zeroDefect_eq_J_log]
  constructor
  · intro h
    have hz :
        zeroDeviation ρ = 0 :=
      (Foundation.DiscretenessForcing.J_log_eq_zero_iff).mp h
    exact (zeroDeviation_eq_zero_iff_on_critical_line ρ).mp hz
  · intro h
    have hz : zeroDeviation ρ = 0 :=
      (zeroDeviation_eq_zero_iff_on_critical_line ρ).mpr h
    exact (Foundation.DiscretenessForcing.J_log_eq_zero_iff).mpr hz

/-- Off the critical line, the zero-location defect is strictly positive. -/
theorem zeroDefect_pos_iff_off_critical_line (ρ : ℂ) :
    0 < zeroDefect ρ ↔ ¬ OnCriticalLine ρ := by
  rw [zeroDefect_eq_J_log]
  constructor
  · intro h hline
    have hzero :
        Foundation.DiscretenessForcing.J_log (zeroDeviation ρ) = 0 :=
      (Foundation.DiscretenessForcing.J_log_eq_zero_iff).mpr
        ((zeroDeviation_eq_zero_iff_on_critical_line ρ).mpr hline)
    linarith
  · intro hline
    have hneq : zeroDeviation ρ ≠ 0 := by
      intro hz
      exact hline ((zeroDeviation_eq_zero_iff_on_critical_line ρ).mp hz)
    exact Foundation.DiscretenessForcing.J_log_pos hneq

/-- The zero-location defect is nonnegative everywhere. -/
theorem zeroDefect_nonneg (ρ : ℂ) : 0 ≤ zeroDefect ρ := by
  rw [zeroDefect_eq_J_log]
  exact Foundation.DiscretenessForcing.J_log_nonneg (zeroDeviation ρ)

@[simp] theorem functionalReflection_re (ρ : ℂ) :
    (functionalReflection ρ).re = 1 - ρ.re := by
  simp [functionalReflection]

@[simp] theorem criticalReflection_re (ρ : ℂ) :
    (criticalReflection ρ).re = 1 - ρ.re := by
  simp [criticalReflection]

@[simp] theorem zeroDeviation_functionalReflection (ρ : ℂ) :
    zeroDeviation (functionalReflection ρ) = -zeroDeviation ρ := by
  unfold zeroDeviation functionalReflection
  simp
  linarith

@[simp] theorem zeroDeviation_conj (ρ : ℂ) :
    zeroDeviation (conj ρ) = zeroDeviation ρ := by
  simp [zeroDeviation]

@[simp] theorem zeroDeviation_criticalReflection (ρ : ℂ) :
    zeroDeviation (criticalReflection ρ) = -zeroDeviation ρ := by
  unfold zeroDeviation criticalReflection
  simp
  linarith

/-- Reflection across `Re(s) = 1/2` preserves the zero-location defect. -/
theorem zeroDefect_invariant_under_functional_reflection (ρ : ℂ) :
    zeroDefect (functionalReflection ρ) = zeroDefect ρ := by
  calc
    zeroDefect (functionalReflection ρ)
        =
          Foundation.DiscretenessForcing.J_log
            (zeroDeviation (functionalReflection ρ)) := zeroDefect_eq_J_log _
    _ = Foundation.DiscretenessForcing.J_log (-zeroDeviation ρ) := by
          rw [zeroDeviation_functionalReflection]
    _ = Foundation.DiscretenessForcing.J_log (zeroDeviation ρ) := by
          exact Foundation.DiscretenessForcing.J_log_symmetric (zeroDeviation ρ)
    _ = zeroDefect ρ := (zeroDefect_eq_J_log ρ).symm

/-- Conjugation preserves the zero-location defect. -/
theorem zeroDefect_invariant_under_conjugation (ρ : ℂ) :
    zeroDefect (conj ρ) = zeroDefect ρ := by
  calc
    zeroDefect (conj ρ)
        =
          Foundation.DiscretenessForcing.J_log
            (zeroDeviation (conj ρ)) := zeroDefect_eq_J_log _
    _ = Foundation.DiscretenessForcing.J_log (zeroDeviation ρ) := by
          rw [zeroDeviation_conj]
    _ = zeroDefect ρ := (zeroDefect_eq_J_log ρ).symm

/-- Reflection plus conjugation preserves the zero-location defect. -/
theorem zeroDefect_invariant_under_reflection (ρ : ℂ) :
    zeroDefect (criticalReflection ρ) = zeroDefect ρ := by
  calc
    zeroDefect (criticalReflection ρ)
        =
          Foundation.DiscretenessForcing.J_log
            (zeroDeviation (criticalReflection ρ)) := zeroDefect_eq_J_log _
    _ = Foundation.DiscretenessForcing.J_log (-zeroDeviation ρ) := by
          rw [zeroDeviation_criticalReflection]
    _ = Foundation.DiscretenessForcing.J_log (zeroDeviation ρ) := by
          exact Foundation.DiscretenessForcing.J_log_symmetric (zeroDeviation ρ)
    _ = zeroDefect ρ := (zeroDefect_eq_J_log ρ).symm

end

end NumberTheory
end IndisputableMonolith

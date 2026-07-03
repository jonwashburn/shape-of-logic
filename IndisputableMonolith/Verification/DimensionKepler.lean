import Mathlib

/-!
# Kepler Specialization for Dimension Selection

This module isolates the algebraic core used by the `(K)` specialization in the
dimensional rigidity paper:

* define the closed-form apsidal-angle expression
  `Δθ(D) = 2π / √(4 - D)`;
* prove `Δθ(D) = 2π ↔ D = 3`.

This is intentionally the reduced-form endpoint theorem (after the classical
mechanics derivation), so it can be referenced from the verification layer.
-/

noncomputable section

namespace IndisputableMonolith
namespace Verification
namespace DimensionKepler

open Real

/-- Closed-form apsidal angle used in the Kepler specialization. -/
noncomputable def apsidalAngle (D : ℕ) : ℝ :=
  (2 * Real.pi) / Real.sqrt (4 - (D : ℝ))

/-- Algebraic Kepler selector: `Δθ = 2π` holds exactly at `D = 3`. -/
theorem kepler_selection_principle (D : ℕ) :
    apsidalAngle D = 2 * Real.pi ↔ D = 3 := by
  constructor
  · intro h
    have hpi : (2 * Real.pi) ≠ 0 := by
      exact mul_ne_zero (by norm_num) Real.pi_ne_zero
    set x : ℝ := Real.sqrt (4 - (D : ℝ))
    have hx : x ≠ 0 := by
      intro hx0
      have : apsidalAngle D = 0 := by
        simp [apsidalAngle, x, hx0]
      have h0 : 0 = 2 * Real.pi := by
        simpa [this] using h
      exact hpi h0.symm
    have h' : (2 * Real.pi) * x⁻¹ = 2 * Real.pi := by
      simpa [apsidalAngle, x, div_eq_mul_inv] using h
    have hmul : (2 * Real.pi) * (x⁻¹ * x) = (2 * Real.pi) * x := by
      simpa [mul_assoc] using congrArg (fun t => t * x) h'
    have hmul' : (2 * Real.pi) = (2 * Real.pi) * x := by
      simpa [mul_assoc, inv_mul_cancel₀ hx, mul_one] using hmul
    have hx1 : x = 1 := by
      have hcancel : (2 * Real.pi) * x = (2 * Real.pi) * 1 := by
        calc
          (2 * Real.pi) * x = (2 * Real.pi) := by simpa [mul_assoc] using hmul'.symm
          _ = (2 * Real.pi) * 1 := by simp
      exact mul_left_cancel₀ hpi hcancel
    have hnonneg : 0 ≤ 4 - (D : ℝ) := by
      by_contra hneg
      have hle : 4 - (D : ℝ) ≤ 0 := le_of_not_ge hneg
      have : Real.sqrt (4 - (D : ℝ)) = 0 := Real.sqrt_eq_zero_of_nonpos hle
      have : (1 : ℝ) = 0 := by simpa [x, hx1] using this
      exact one_ne_zero this
    have hsq : x ^ 2 = 4 - (D : ℝ) := by
      simpa [x, pow_two] using (Real.sq_sqrt hnonneg)
    have hreal : (D : ℝ) = 3 := by
      have : (1 : ℝ) ^ 2 = 4 - (D : ℝ) := by simpa [hx1] using hsq
      nlinarith
    exact (Nat.cast_injective (R := ℝ) (by simpa using hreal))
  · intro hD
    subst hD
    have : (4 - (3 : ℝ)) = (1 : ℝ) := by norm_num
    simp [apsidalAngle, this]

end DimensionKepler
end Verification
end IndisputableMonolith


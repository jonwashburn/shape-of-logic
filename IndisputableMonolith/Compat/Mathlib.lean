import Mathlib

/-!
Compatibility shims and common mathlib imports.

This module collects small alias lemmas and helpers to stabilize names
across mathlib versions and reduce duplication across the codebase.
-/

open scoped BigOperators Matrix
open Real Complex

-- Aliases and small helpers (avoid redefining Mathlib lemmas)

theorem one_div_pos_of_pos' {x : ℝ} (hx : 0 < x) : 0 < 1 / x := by
  simpa [one_div] using inv_pos.mpr hx

theorem one_div_nonneg_of_nonneg' {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 / x := by
  simpa [one_div] using inv_nonneg.mpr hx

theorem Real.rpow_nonneg_of_nonneg' {x a : ℝ} (hx : 0 ≤ x) : 0 ≤ x ^ a := by
  simpa using Real.rpow_nonneg hx a

theorem Real.rpow_lt_one_of_pos_of_lt_one' {x y : ℝ}
    (hx_pos : 0 < x) (hx_lt_one : x < 1) (hy_pos : 0 < y) :
    x ^ y < 1 := by
  exact Real.rpow_lt_one hx_pos.le hx_lt_one hy_pos

-- Common simp-normalizations for division forms
theorem one_div_mul' (x y : ℝ) : (1 / x) * y = y / x := by
  ring

theorem inv_pos_iff_one_div_pos' {x : ℝ} : (0 < x⁻¹) ↔ (0 < 1 / x) := by
  simp [one_div]

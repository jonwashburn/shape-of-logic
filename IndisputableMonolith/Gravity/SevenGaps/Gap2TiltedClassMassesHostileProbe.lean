/-
Copyright (c) 2026 Recognition Physics Institute. All rights reserved.
Author: Jonathan Washburn
-/
import IndisputableMonolith.Gravity.SevenGaps.Gap2TiltedClassMasses
import Mathlib.Tactic.NormNum

/-!
# Hostile probe: Gap2TiltedClassMasses (C32)

Uncommitted review probe. Verifies the projected `M(0;3)` / `M(0;4)` rationals
against the independent Bigbird recomputation, and that this module does not
touch `FullTheoryLedger` (import graph: only `Gap2TiltedClassMasses`).
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2TiltedClassMassesHostileProbe

open Gap2TiltedClassMasses

/-- Independent recomputation: `M(0;3) = 265/6`. -/
theorem hostile_M0_cap3 : M0_cap3 = (265 : ℚ) / 6 := M0_cap3_eq

/-- Independent recomputation: `M(0;4) = 35045/144`. -/
theorem hostile_M0_cap4 : M0_cap4 = (35045 : ℚ) / 144 := M0_cap4_eq

/-- Decimal cross-check bounds used in the A23 report. -/
theorem hostile_M0_cap3_decimal_bound :
    (44 : ℚ) < M0_cap3 ∧ M0_cap3 < (45 : ℚ) := by
  constructor <;> native_decide

theorem hostile_M0_cap4_decimal_bound :
    (243 : ℚ) < M0_cap4 ∧ M0_cap4 < (244 : ℚ) := by
  constructor <;> native_decide

theorem hostile_nClasses :
    nClassesCap3 = 68 ∧ nClassesCap4 = 437 := by
  constructor <;> rfl

/-- Sanity: projected masses are strictly increasing in the cap. -/
theorem hostile_M0_mono : M0_cap3 < M0_cap4 := M0_cap3_lt_M0_cap4

end Gap2TiltedClassMassesHostileProbe
end SevenGaps
end Gravity
end IndisputableMonolith

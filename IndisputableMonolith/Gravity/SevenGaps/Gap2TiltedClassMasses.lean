/-
Copyright (c) 2026 Recognition Physics Institute. All rights reserved.
Author: Jonathan Washburn
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# Gap 2 / C32: tilted class-mass headline numbers (cap ≤ 4)

Projection of the MEASURED partition function

    M(t; cap) = ∑_{iso classes K} (1/|Aut K|) · exp(-t · SJ(K))

at `t = 0`, where the sum runs over tet-free directed posting graphs with
`nV ≤ cap` and `nE ≤ cap`.  At `t = 0` this is the total μ-mass of those
classes.  Exact values (Bigbird enumeration + directed Aut, receipt
`scripts/qg/out/tilted_class_masses_20260730.json`):

* `M(0; 3) = 265/6`
* `M(0; 4) = 35045/144`

No continuum / scaling-window claim is projected here: the measurement found
no log-log scaling window on the `(t, cap)` grid at `cap ≤ 4` (outcome
`no_window`).  `FullTheoryLedger` is untouched.  Tier: MEASURED projection
of exact rationals; the Aut census itself is not re-derived in-kernel.
-/

namespace IndisputableMonolith
namespace Gravity
namespace SevenGaps
namespace Gap2TiltedClassMasses

/-- Total μ-mass `M(0; 3)` of tet-free directed classes at cap 3. -/
def M0_cap3 : ℚ := 265 / 6

/-- Total μ-mass `M(0; 4)` of tet-free directed classes at cap 4. -/
def M0_cap4 : ℚ := 35045 / 144

theorem M0_cap3_eq : M0_cap3 = (265 : ℚ) / 6 := rfl

theorem M0_cap4_eq : M0_cap4 = (35045 : ℚ) / 144 := rfl

theorem M0_cap3_pos : (0 : ℚ) < M0_cap3 := by native_decide

theorem M0_cap4_pos : (0 : ℚ) < M0_cap4 := by native_decide

theorem M0_cap3_lt_M0_cap4 : M0_cap3 < M0_cap4 := by native_decide

/-- Cap-3 / cap-4 unweighted class counts from the C15/C32 census (MEASURED). -/
def nClassesCap3 : ℕ := 68
def nClassesCap4 : ℕ := 437

end Gap2TiltedClassMasses
end SevenGaps
end Gravity
end IndisputableMonolith

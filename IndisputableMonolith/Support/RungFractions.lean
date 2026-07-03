import Mathlib

/-!
# Fractional φ-Ladder Rungs (Convention / Reporting Seam)

This file provides a minimal, *type-light* representation for fractional rungs on the φ‑ladder.

Why it exists:
- The **core** mass model layer uses integer rungs (`ℤ`) for maximal rigidity.
- Some physics modules (quark masses, neutrino deep ladder refinements) explore **fractional**
  placements (e.g. quarter-ladder) to capture observed ratios.

This is **not** (yet) a proof that fractional rungs are canonical. It is a *representation seam*:
we make the convention explicit and mechanically uniform across modules.
-/

namespace IndisputableMonolith
namespace Support
namespace RungFractions

/-- A (possibly fractional) rung on the φ‑ladder. -/
abbrev Rung := ℚ

/-- Embed an integer rung into a rational rung. -/
@[simp] def ofInt (z : ℤ) : Rung := (z : ℚ)

/-- The quarter‑ladder embedding: `k ↦ k/4`. -/
@[simp] def quarter (k : ℤ) : Rung := (k : ℚ) / 4

/-- The half‑ladder embedding: `k ↦ k/2`. -/
@[simp] def half (k : ℤ) : Rung := (k : ℚ) / 2

/-- Convert a rational rung to a real exponent (for `Real.rpow`). -/
@[simp] def toReal (r : Rung) : ℝ := (r : ℝ)

theorem quarter_eq (k : ℤ) : quarter k = (k : ℚ) / 4 := rfl
theorem half_eq (k : ℤ) : half k = (k : ℚ) / 2 := rfl

end RungFractions
end Support
end IndisputableMonolith

import Mathlib

/-!
# Preregistered Test Harness (Core)

Design goal: enforce “formula frozen before measurement” structurally.

- **Predictions** live in modules that do **not** import measurement modules.
- **Measurements** live in separate modules (pure data).
- **Tests** import both.

This doesn’t prove historical preregistration, but it enforces a clean, auditable
separation inside the Lean build graph.
-/

namespace IndisputableMonolith
namespace Verification
namespace Preregistered

structure IntervalPrediction where
  name : String
  lo : ℝ
  hi : ℝ

structure PointPrediction where
  name : String
  val : ℝ

structure Measurement where
  name : String
  central : ℝ
  sigma : ℝ

def interval_contains (p : IntervalPrediction) (m : Measurement) : Prop :=
  p.lo < m.central ∧ m.central < p.hi

def within_sigma (p : PointPrediction) (m : Measurement) (k : ℝ := 1) : Prop :=
  |p.val - m.central| < k * m.sigma

end Preregistered
end Verification
end IndisputableMonolith

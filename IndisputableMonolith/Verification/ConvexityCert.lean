import Mathlib
import IndisputableMonolith.Cost.Convexity

namespace IndisputableMonolith
namespace Verification
namespace Convexity

open IndisputableMonolith.Cost
open Real Set

/-!
# Convexity Certificate: Strict Convexity (A3)

This certificate packages the proofs that cosh and Jlog are strictly convex,
which is axiom A3 in the uniqueness theorem T5.

## Key Results

1. `StrictConvexOn ℝ univ Real.cosh` — cosh is strictly convex on ℝ
2. `StrictConvexOn ℝ univ Jlog` — Jlog is strictly convex on ℝ
3. `StrictConvexOn ℝ (Ioi 0) Jcost` — Jcost is strictly convex on ℝ₊

## Why this matters for the certificate chain

Strict convexity guarantees that:
- The minimum at the origin is unique
- No other cost function with the same symmetry properties can exist
- The cost function is bowl-shaped with a single global minimum

The proof uses the second derivative test:
- cosh''(t) = cosh(t) > 0 for all t
- Therefore cosh is strictly convex
- Jlog = cosh - 1, so Jlog inherits strict convexity

## Mathematical Content

For Jcost on ℝ₊:
- J''(x) = x⁻³ > 0 for x > 0
- Therefore Jcost is strictly convex on (0, ∞)
-/

structure ConvexityCert where
  deriving Repr

/-- Verification predicate: cosh and Jlog are strictly convex.

This certifies:
1. cosh is strictly convex on ℝ
2. Jlog is strictly convex on ℝ
3. Jcost is strictly convex on (0, ∞) -/
@[simp] def ConvexityCert.verified (_c : ConvexityCert) : Prop :=
  -- cosh is strictly convex on ℝ
  StrictConvexOn ℝ univ Real.cosh ∧
  -- Jlog is strictly convex on ℝ
  StrictConvexOn ℝ univ Jlog ∧
  -- Jcost is strictly convex on (0, ∞)
  StrictConvexOn ℝ (Ioi (0 : ℝ)) Jcost

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem ConvexityCert.verified_any (c : ConvexityCert) :
    ConvexityCert.verified c := by
  refine ⟨?_, ?_, ?_⟩
  · exact cosh_strictly_convex
  · exact Jlog_strictConvexOn
  · exact Jcost_strictConvexOn_pos

end Convexity
end Verification
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Cost.Convexity

/-!
# Jcost Strict Convexity Certificate

This audit certificate packages the **strict convexity** of the original cost function:

\[
  J(x) = \frac{x + x^{-1}}{2} - 1 \text{ is strictly convex on } (0, \infty)
\]

## Why this matters for the certificate chain

This certifies the strict convexity of Jcost in its natural domain (positive reals):

1. **Unique minimum at x = 1**: Strict convexity implies J has at most one critical point
2. **Second derivative test**: J''(x) = x⁻³ > 0 for all x > 0
3. **Complements Jlog**: While Jlog is strictly convex on all of ℝ, Jcost is
   strictly convex on (0, ∞) — these are equivalent via log/exp correspondence

## Proof approach

A function with positive second derivative on a convex set is strictly convex.
For Jcost:
- First derivative: J'(x) = (1 - x⁻²)/2
- Second derivative: J''(x) = x⁻³ > 0 for x > 0
- Therefore Jcost is strictly convex on (0, ∞)
-/

namespace IndisputableMonolith
namespace Verification
namespace JcostStrictConvex

open IndisputableMonolith.Cost
open Set

structure JcostStrictConvexCert where
  deriving Repr

/-- Verification predicate: Jcost is strictly convex on (0, ∞).

This certifies the strict convexity of the cost function on positive reals. -/
@[simp] def JcostStrictConvexCert.verified (_c : JcostStrictConvexCert) : Prop :=
  StrictConvexOn ℝ (Ioi (0 : ℝ)) Jcost

@[simp] theorem JcostStrictConvexCert.verified_any (c : JcostStrictConvexCert) :
    JcostStrictConvexCert.verified c := by
  exact Jcost_strictConvexOn_pos

end JcostStrictConvex
end Verification
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Cost.Convexity

/-!
# J-cost Strict Convexity Certificate

This audit certificate packages the **strict convexity** of the RS cost kernel:

\[
  J(x) = \frac{x + x^{-1}}{2} - 1
\]

is strictly convex on \((0, \infty)\).

## Why this matters for the certificate chain

Strict convexity of the cost function is central to uniqueness arguments in Recognition
Science. If J were merely convex (not strictly), there could be multiple minimizers or
flat regions. Strict convexity ensures:

1. **Unique minimum**: J has exactly one critical point (at x = 1, where J(1) = 0)
2. **Optimization uniqueness**: Any cost-minimization problem using J has a unique solution
3. **T5 foundation**: The uniqueness theorem (T5) relies on strict convexity to establish
   that the RS cost kernel is the unique symmetric, normalized, strictly convex function
   agreeing with the averaging kernel

## Proof approach

The strict convexity is proven via the second derivative test:
- J''(x) = x^{-3} > 0 for all x > 0
- A function with positive second derivative on a convex domain is strictly convex
-/

namespace IndisputableMonolith
namespace Verification
namespace JcostConvexity

open Set

structure JcostConvexityCert where
  deriving Repr

/-- Verification predicate: J-cost is strictly convex on (0, ∞). -/
@[simp] def JcostConvexityCert.verified (_c : JcostConvexityCert) : Prop :=
  StrictConvexOn ℝ (Ioi (0 : ℝ)) IndisputableMonolith.Cost.Jcost

@[simp] theorem JcostConvexityCert.verified_any (c : JcostConvexityCert) :
    JcostConvexityCert.verified c := by
  exact IndisputableMonolith.Cost.Jcost_strictConvexOn_pos

end JcostConvexity
end Verification
end IndisputableMonolith

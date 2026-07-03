import Mathlib
import IndisputableMonolith.Cost.Convexity

/-!
# Cosh Strict Convexity Certificate

This audit certificate packages the **strict convexity** of the hyperbolic cosine:

\[
  \cosh : \mathbb{R} \to \mathbb{R} \text{ is strictly convex on } \mathbb{R}
\]

## Why this matters for the certificate chain

The hyperbolic cosine is the foundational function underlying the J-cost structure:

1. **Jlog = cosh - 1**: The log-domain cost is cosh shifted down by 1
2. **cosh'' = cosh > 0**: The second derivative is always positive
3. **Strict convexity of Jlog**: Follows directly from cosh's strict convexity

This provides the analytical foundation for the uniqueness of the cost minimum:
since cosh is strictly convex and Jlog = cosh - 1, the cost function inherits
strict convexity, guaranteeing a unique global minimum.

## Proof approach

A function with positive second derivative on a convex set is strictly convex.
For cosh:
- First derivative: cosh' = sinh
- Second derivative: cosh'' = cosh > 0 everywhere
- Therefore cosh is strictly convex on ℝ
-/

namespace IndisputableMonolith
namespace Verification
namespace CoshStrictConvex

open Set

structure CoshStrictConvexCert where
  deriving Repr

/-- Verification predicate: cosh is strictly convex on ℝ.

This certifies the strict convexity of the hyperbolic cosine function. -/
@[simp] def CoshStrictConvexCert.verified (_c : CoshStrictConvexCert) : Prop :=
  StrictConvexOn ℝ univ Real.cosh

@[simp] theorem CoshStrictConvexCert.verified_any (c : CoshStrictConvexCert) :
    CoshStrictConvexCert.verified c := by
  exact IndisputableMonolith.Cost.cosh_strictly_convex

end CoshStrictConvex
end Verification
end IndisputableMonolith

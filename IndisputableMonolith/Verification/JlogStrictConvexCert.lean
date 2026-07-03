import Mathlib
import IndisputableMonolith.Cost.Convexity

/-!
# Jlog Strict Convexity Certificate

This audit certificate packages the **strict convexity** of the log-domain cost:

\[
  J_{\log} : \mathbb{R} \to \mathbb{R} \text{ is strictly convex on } \mathbb{R}
\]

## Why this matters for the certificate chain

Strict convexity is a powerful property that implies:

1. **Unique global minimum**: Any critical point is the unique global minimizer
2. **Gradient characterization**: ∇Jlog(t) = 0 ⟺ t is the unique minimizer
3. **Strong duality**: For optimization problems involving Jlog

Combined with JlogZeroCert (Jlog(0) = 0) and JlogNonnegCert (Jlog ≥ 0),
strict convexity provides an independent route to uniqueness of the cost minimum.

## Proof approach

Since Jlog(t) = cosh(t) - 1:
1. cosh is strictly convex on ℝ (second derivative cosh'' = cosh > 0)
2. Subtracting a constant preserves strict convexity
3. Therefore Jlog = cosh - 1 is strictly convex on ℝ
-/

namespace IndisputableMonolith
namespace Verification
namespace JlogStrictConvex

open IndisputableMonolith.Cost
open Set

structure JlogStrictConvexCert where
  deriving Repr

/-- Verification predicate: Jlog is strictly convex on ℝ.

This certifies the strict convexity of the log-domain cost function. -/
@[simp] def JlogStrictConvexCert.verified (_c : JlogStrictConvexCert) : Prop :=
  StrictConvexOn ℝ univ Jlog

@[simp] theorem JlogStrictConvexCert.verified_any (c : JlogStrictConvexCert) :
    JlogStrictConvexCert.verified c := by
  exact Jlog_strictConvexOn

end JlogStrictConvex
end Verification
end IndisputableMonolith

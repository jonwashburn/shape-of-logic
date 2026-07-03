import Mathlib
import IndisputableMonolith.Cost

/-!
# J-cost Unique Minimum Certificate

This audit certificate packages the **unique minimum** property of the RS cost kernel:

\[
  J(x) = \frac{x + x^{-1}}{2} - 1
\]

has a unique global minimum at x = 1, where J(1) = 0.

## Why this matters for the certificate chain

The J-cost function is the fundamental "deviation cost" in Recognition Science:
- J(1) = 0: No cost at the identity (perfect recognition)
- J(x) > 0 for x ≠ 1: Any deviation from identity incurs positive cost

Together with strict convexity (JcostConvexityCert), this establishes that:
1. The identity is the unique optimal state
2. All deviations are penalized
3. There are no other local minima

## Proof approach

The key identity is J(x) = (x - 1)² / (2x), which shows:
- Numerator (x - 1)² ≥ 0, with equality iff x = 1
- Denominator 2x > 0 for x > 0
- Therefore J(x) ≥ 0 with J(x) = 0 iff x = 1
-/

namespace IndisputableMonolith
namespace Verification
namespace JcostMinimum

open IndisputableMonolith.Cost

structure JcostMinimumCert where
  deriving Repr

/-- Verification predicate: J has a unique minimum at x = 1.

This asserts:
1. J(1) = 0 (the minimum value)
2. For all x > 0 with x ≠ 1, we have J(x) > 0 (strict positivity away from minimum)
-/
@[simp] def JcostMinimumCert.verified (_c : JcostMinimumCert) : Prop :=
  (Jcost 1 = 0) ∧
  (∀ x : ℝ, 0 < x → x ≠ 1 → 0 < Jcost x)

@[simp] theorem JcostMinimumCert.verified_any (c : JcostMinimumCert) :
    JcostMinimumCert.verified c := by
  constructor
  · -- J(1) = 0
    exact Jcost_unit0
  · -- J(x) > 0 for x > 0, x ≠ 1
    intro x hx hx1
    exact Jcost_pos_of_ne_one x hx hx1

end JcostMinimum
end Verification
end IndisputableMonolith

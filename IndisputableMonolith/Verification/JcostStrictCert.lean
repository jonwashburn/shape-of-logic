import Mathlib
import IndisputableMonolith.Cost

namespace IndisputableMonolith
namespace Verification
namespace JcostStrict

open IndisputableMonolith.Cost

/-!
# Jcost Strict Positivity Certificate

This certificate packages the strict positivity result for Jcost that
strengthens the minimum uniqueness story.

## Key Result

**Strict Positivity**: J(x) > 0 for x ≠ 1 and x > 0

## Why this matters for the certificate chain

We already know:
- J(x) ≥ 0 for x > 0 (certified in JcostAxiomsCert)
- J(1) = 0 (certified in JcostAxiomsCert)

This certificate adds the strict version:
- J(x) = 0 **only** at x = 1 (strict positivity elsewhere)

This proves that x = 1 is the **unique global minimum**.

## Mathematical Content

From J(x) = (x-1)²/(2x):
- Numerator (x-1)² > 0 when x ≠ 1 (strict positivity of squares)
- Denominator 2x > 0 when x > 0
- Therefore J(x) > 0 when x ≠ 1 and x > 0
-/

structure JcostStrictCert where
  deriving Repr

/-- Verification predicate: Jcost has strict positivity away from 1.

This certifies: J(x) > 0 for x ≠ 1 and x > 0 -/
@[simp] def JcostStrictCert.verified (_c : JcostStrictCert) : Prop :=
  -- Strict positivity: J(x) > 0 for x ≠ 1, x > 0
  ∀ x : ℝ, 0 < x → x ≠ 1 → 0 < Jcost x

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem JcostStrictCert.verified_any (c : JcostStrictCert) :
    JcostStrictCert.verified c := by
  intro x hx hx1
  exact Jcost_pos_of_ne_one x hx hx1

end JcostStrict
end Verification
end IndisputableMonolith

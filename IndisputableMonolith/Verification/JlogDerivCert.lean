import Mathlib
import IndisputableMonolith.Cost

/-!
# Jlog Derivative Certificate

This audit certificate packages the **derivative formula** for the log-domain cost:

\[
  \frac{d}{dt} J_{\log}(t) = \sinh(t)
\]

## Why this matters for the certificate chain

The derivative formula connects Jlog to the hyperbolic sine:

1. **Critical point**: At t = 0, sinh(0) = 0, so Jlog'(0) = 0 (stationary point)
2. **Sign analysis**: sinh(t) < 0 for t < 0, sinh(t) > 0 for t > 0
   - This proves t = 0 is a local minimum
3. **Monotonicity**: Jlog is decreasing on (-∞, 0) and increasing on (0, ∞)

Combined with strict convexity, this provides the calculus-based proof that
t = 0 is the unique global minimum.

## Proof approach

Since Jlog(t) = cosh(t) - 1:
- d/dt cosh(t) = sinh(t)
- d/dt (-1) = 0
- Therefore d/dt Jlog(t) = sinh(t)
-/

namespace IndisputableMonolith
namespace Verification
namespace JlogDeriv

open IndisputableMonolith.Cost

structure JlogDerivCert where
  deriving Repr

/-- Verification predicate: The derivative of Jlog at t is sinh(t).

This certifies the derivative formula for the log-domain cost function. -/
@[simp] def JlogDerivCert.verified (_c : JlogDerivCert) : Prop :=
  ∀ t : ℝ, HasDerivAt Jlog (Real.sinh t) t

@[simp] theorem JlogDerivCert.verified_any (c : JlogDerivCert) :
    JlogDerivCert.verified c := by
  intro t
  exact hasDerivAt_Jlog t

end JlogDeriv
end Verification
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Verification
namespace ODEFoundation

open IndisputableMonolith.Cost.FunctionalEquation
open Real

/-!
# ODE Foundation Certificate: Zero Uniqueness and Even Derivative

This certificate packages the foundational ODE uniqueness results that
underpin the cosh uniqueness theorem.

## Key Results

1. **ODE Zero Uniqueness**: f'' = f with f(0) = 0, f'(0) = 0 implies f = 0
2. **Even Derivative Zero**: Even function H differentiable at 0 implies H'(0) = 0

## Why this matters for the certificate chain

These are the core lemmas that make the ODE cosh uniqueness proof work:

1. **ODE Zero Uniqueness** shows that homogeneous initial conditions give
   the zero solution. This is used to prove cosh uniqueness by taking
   H - cosh and showing it's zero.

2. **Even Derivative Zero** provides the H'(0) = 0 initial condition from
   the symmetry (evenness) of the cost function in log-coordinates.

The proof of ODE Zero Uniqueness uses a beautiful diagonalization trick:
- Write f' - f and f' + f as the "eigencomponents"
- These satisfy g' = -g and h' = h respectively
- With zero initial conditions, both must be zero
- Therefore f = 0

## Mathematical Content

For g' = -g with g(0) = 0:
- Consider g(t) · exp(t), which has zero derivative
- So g(t) · exp(t) = g(0) · exp(0) = 0
- Therefore g(t) = 0

Similarly for h' = h with h(0) = 0.
-/

structure ODEFoundationCert where
  deriving Repr

/-- Verification predicate: ODE zero uniqueness and even derivative zero.

This certifies:
1. f'' = f with f(0) = f'(0) = 0 implies f = 0 everywhere
2. Even H with H differentiable at 0 implies H'(0) = 0 -/
@[simp] def ODEFoundationCert.verified (_c : ODEFoundationCert) : Prop :=
  -- ODE zero uniqueness
  (∀ f : ℝ → ℝ,
    ContDiff ℝ 2 f →
    (∀ t, deriv (deriv f) t = f t) →
    f 0 = 0 →
    deriv f 0 = 0 →
    ∀ t, f t = 0) ∧
  -- Even derivative at zero
  (∀ H : ℝ → ℝ,
    Function.Even H →
    DifferentiableAt ℝ H 0 →
    deriv H 0 = 0)

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem ODEFoundationCert.verified_any (c : ODEFoundationCert) :
    ODEFoundationCert.verified c := by
  constructor
  · intro f h1 h2 h3 h4
    exact ode_zero_uniqueness f h1 h2 h3 h4
  · intro H h1 h2
    exact even_deriv_at_zero H h1 h2

end ODEFoundation
end Verification
end IndisputableMonolith

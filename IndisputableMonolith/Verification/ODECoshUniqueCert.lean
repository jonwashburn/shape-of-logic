import Mathlib
import IndisputableMonolith.Cost.FunctionalEquation

namespace IndisputableMonolith
namespace Verification
namespace ODECoshUnique

open IndisputableMonolith.Cost.FunctionalEquation

/-!
# ODE Cosh Uniqueness Certificate

This certificate packages the proof that cosh is the **unique** C² solution to
the second-order ODE:

  H''(t) = H(t)

with initial conditions H(0) = 1 and H'(0) = 0.

## Why this matters for the certificate chain

This uniqueness theorem is foundational for the T5 cost uniqueness proof:

1. **Jlog = cosh - 1**: The log-coordinate cost function Jlog(t) equals cosh(t) - 1

2. **ODE characterization**: Any function satisfying the d'Alembert functional equation
   and regularity conditions must satisfy H'' = H

3. **Uniqueness**: This certificate proves that cosh is the ONLY such function,
   which means Jlog is uniquely determined (up to the constant shift)

4. **No free parameters**: The ODE + initial conditions fully specify the solution -
   there are no parameters to tune

## Proven Results

1. `ode_zero_uniqueness`: The unique C² solution to f'' = f with f(0) = f'(0) = 0 is f ≡ 0
2. `cosh_second_deriv_eq`: cosh'' = cosh (cosh satisfies the ODE)
3. `cosh_initials`: cosh(0) = 1 and cosh'(0) = 0 (cosh satisfies the initial conditions)
4. `ode_cosh_uniqueness_contdiff`: Any C² solution with H(0) = 1, H'(0) = 0 equals cosh
-/

structure ODECoshUniqueCert where
  deriving Repr

/-- Verification predicate: cosh is the unique solution to its defining ODE.

This certifies:
1. The ODE f'' = f with zero initial data has only the zero solution
2. cosh satisfies cosh'' = cosh and cosh(0) = 1, cosh'(0) = 0
3. Any C² function satisfying the ODE with the same initial conditions equals cosh
-/
@[simp] def ODECoshUniqueCert.verified (_c : ODECoshUniqueCert) : Prop :=
  -- 1) Zero uniqueness: f'' = f with f(0) = f'(0) = 0 implies f = 0
  (∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
    (∀ t, deriv (deriv f) t = f t) →
    f 0 = 0 →
    deriv f 0 = 0 →
    ∀ t, f t = 0) ∧
  -- 2) cosh satisfies the ODE: cosh'' = cosh
  (∀ t : ℝ, deriv (deriv Real.cosh) t = Real.cosh t) ∧
  -- 3) cosh satisfies initial conditions
  (Real.cosh 0 = 1 ∧ deriv Real.cosh 0 = 0) ∧
  -- 4) Cosh uniqueness: H'' = H with H(0) = 1, H'(0) = 0 implies H = cosh
  (∀ H : ℝ → ℝ, ContDiff ℝ 2 H →
    (∀ t, deriv (deriv H) t = H t) →
    H 0 = 1 →
    deriv H 0 = 0 →
    ∀ t, H t = Real.cosh t)

/-- Top-level theorem: the certificate verifies. -/
@[simp] theorem ODECoshUniqueCert.verified_any (c : ODECoshUniqueCert) :
    ODECoshUniqueCert.verified c := by
  constructor
  · -- Zero uniqueness
    intro f h_diff h_ode h_f0 h_f'0
    exact ode_zero_uniqueness f h_diff h_ode h_f0 h_f'0
  constructor
  · -- cosh'' = cosh
    exact cosh_second_deriv_eq
  constructor
  · -- cosh initial conditions
    constructor
    · exact Real.cosh_zero
    · have h := Real.deriv_cosh
      simp only [h, Real.sinh_zero]
  · -- Cosh uniqueness
    intro H h_diff h_ode h_H0 h_H'0
    exact ode_cosh_uniqueness_contdiff H h_diff h_ode h_H0 h_H'0

end ODECoshUnique
end Verification
end IndisputableMonolith

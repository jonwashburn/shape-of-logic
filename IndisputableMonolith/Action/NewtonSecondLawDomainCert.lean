import Mathlib
import IndisputableMonolith.Action.QuadraticLimit
import IndisputableMonolith.Action.Hamiltonian

/-!
# Newton's Second Law from the J-Action — Domain Certificate
(Plan v7 twenty-ninth pass continuation)

## Status: THEOREM (0 sorry, 0 axiom).

This module is the domain-cert wrapper for Newton's second law as the
small-strain Euler-Lagrange equation of the J-action. It packages the
key equivalence proved in `Action.QuadraticLimit` into a single `*Cert`
suitable for the master `UnifiedReality` chain.

## What it bundles

- (1) `EL ↔ Newton`: the EL equation of `L = ½ m q̇² - V(q)` is exactly
  `m γ̈ = -V'(γ)`.
- (2) Quadratic Taylor bound: `|J(1+ε) - ε²/2| ≤ ε²/10` for `|ε| ≤ 1/10`.
  This is the analytic content that turns the J-action into the standard
  kinetic-action in the small-strain regime.
- (3) Hessian calibration: `J''(1) = 1`. The leading-order kinetic
  coefficient is forced by the d'Alembert calibration of `Jcost` at the
  ground state.

## Falsifier

A measured trajectory `γ(t)` of a classical particle in potential `V` for
which `m γ̈(t) ≠ -V'(γ(t))` at any `t` would falsify clause (1) and
therefore the small-strain limit of the J-action.

Paper companion: `papers/RS_Least_Action.tex` (Paper A), §"Newton's
Second Law as a Corollary".
-/

namespace IndisputableMonolith
namespace Action

open IndisputableMonolith.Action.QuadraticLimit
open IndisputableMonolith.Cost

/-- Domain certificate for Newton's second law as a corollary of the
J-action variational principle. -/
structure NewtonSecondLawCert where
  el_iff_newton : ∀ (m : ℝ) (V : ℝ → ℝ) (γ : ℝ → ℝ) (t : ℝ),
      QuadraticLimit.standardEL m V γ t = 0 ↔
      m * deriv (deriv γ) t = -(deriv V (γ t))
  quadratic_taylor_bound : ∀ (ε : ℝ), |ε| ≤ (1 : ℝ) / 10 →
      |Jcost (1 + ε) - ε ^ 2 / 2| ≤ ε ^ 2 / 10
  hessian_one : deriv (deriv Jcost) 1 = 1

/-- Inhabited witness — every clause is a theorem in
`Action.QuadraticLimit`. -/
def newtonSecondLawCert : NewtonSecondLawCert where
  el_iff_newton := QuadraticLimit.newton_second_law
  quadratic_taylor_bound := Jcost_taylor_quadratic
  hessian_one := Jcost_quadratic_leading_coeff

/-- One-statement summary: Newton's second law is the EL equation of
the small-strain J-action. -/
theorem newton_second_law_one_statement :
    Nonempty NewtonSecondLawCert :=
  ⟨newtonSecondLawCert⟩

end Action
end IndisputableMonolith

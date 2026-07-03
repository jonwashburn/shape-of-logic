import Mathlib
import IndisputableMonolith.Action.PathSpace
import IndisputableMonolith.Action.FunctionalConvexity
import IndisputableMonolith.Action.EulerLagrange
import IndisputableMonolith.Action.QuadraticLimit
import IndisputableMonolith.Action.Hamiltonian
import IndisputableMonolith.Verification.LeastActionCert

/-!
# Principle of Least Action — Domain Certificate (Plan v7 twenty-ninth pass)

## Status: THEOREM (0 sorry, 0 axiom).

This module is the domain-cert wrapper for the 2026-04-21 closure of the
principle of least action as a theorem of the d'Alembert functional
equation (via convexity of `Jcost`). It packages the headline content
of the `Action.*` namespace into a single `*Cert` structure suitable
for inhabitation in the master `UnifiedReality` chain.

## What it bundles

- (1) Pointwise convexity of the J-action under endpoint-fixing
  interpolation: `S[(1-s) γ₁ + s γ₂] ≤ (1-s) S[γ₁] + s S[γ₂]`.
- (2) Local-to-global minimisation: a path that does not strictly
  decrease the J-action toward any competitor (along even one positive
  interpolation step) globally minimises the action.
- (3) The cost-rate Euler-Lagrange equation has unique solution `γ ≡ 1`.

These are exactly the three convexity-anchored clauses of
`Verification.LeastActionCert`. Newton's second law and energy
conservation are isolated in their own domain certs (Plan v7 twenty-ninth
pass continuation), so this cert focuses on the variational principle
itself.

## Falsifier

Any path `γ_other` of strictly lower J-action than the constant `γ ≡ 1`
on a fixed-endpoint interval where `γ_other(a) = γ_other(b) = 1`
falsifies the convexity bound and therefore falsifies the d'Alembert
uniqueness underlying `Cost.Jcost`.

Paper companion: `papers/RS_Least_Action.tex` (Paper A).
-/

namespace IndisputableMonolith
namespace Action

open IndisputableMonolith.Action
open IndisputableMonolith.Verification.LeastAction

/-- Domain certificate for the principle of least action.

The three load-bearing fields:

* `convexity` — convexity of `actionJ` under `interp`-interpolation.
* `local_to_global` — local minimisation along one positive interpolation
  step implies global minimisation against the same competitor.
* `costRate_unique` — the cost-rate EL equation has the constant ground
  state as its unique positive solution.

Each field is unconditional in the active codebase; the `Cost.Jcost`
strict convexity is a theorem (Aczel + d'Alembert), and the action
inherits convexity by integrating the pointwise bound. -/
structure PrincipleLeastActionCert where
  convexity : ∀ {a b : ℝ} (hab : a ≤ b) (γ₁ γ₂ : AdmissiblePath a b)
      (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1),
      actionJ (interp γ₁ γ₂ s hs) ≤ (1 - s) * actionJ γ₁ + s * actionJ γ₂
  local_to_global : ∀ {a b : ℝ} (hab : a ≤ b)
      (γ_geo γ_other : AdmissiblePath a b)
      (s₀ : ℝ) (hs₀ : s₀ ∈ Set.Icc (0:ℝ) 1) (_hs₀_pos : 0 < s₀),
      actionJ γ_geo ≤ actionJ (interp γ_geo γ_other s₀ hs₀) →
      actionJ γ_geo ≤ actionJ γ_other
  costRate_unique : ∀ (γ : ℝ → ℝ), (∀ t, 0 < γ t) →
      (EulerLagrange.costRateELHolds γ ↔ ∀ t, γ t = 1)

/-- Inhabited witness — every clause is a theorem in
`Action.FunctionalConvexity` / `Action.EulerLagrange`. -/
def principleLeastActionCert : PrincipleLeastActionCert where
  convexity := by
    intro a b hab γ₁ γ₂ s hs
    exact actionJ_convex_on_interp hab γ₁ γ₂ s hs
  local_to_global := by
    intro a b hab γ_geo γ_other s₀ hs₀ hs₀_pos h_local
    exact actionJ_local_min_is_global hab γ_geo γ_other s₀ hs₀ hs₀_pos h_local
  costRate_unique := by
    intro γ hpos
    exact EulerLagrange.costRateEL_iff_const_one γ hpos

/-- One-statement summary: the principle of least action is a theorem
of d'Alembert uniqueness. -/
theorem principle_least_action_one_statement :
    Nonempty PrincipleLeastActionCert :=
  ⟨principleLeastActionCert⟩

end Action
end IndisputableMonolith

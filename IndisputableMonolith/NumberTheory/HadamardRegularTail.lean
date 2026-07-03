import IndisputableMonolith.NumberTheory.HadamardGenusOne

/-!
  HadamardRegularTail.lean

  From a `XiHadamardIdentification` we want to split `ξ₀` at any chosen
  zero index `k` into a local elementary factor `E₁(s/zeros k)` and a
  regular tail consisting of the remaining genus-one product times the
  exponential prefactor.

  Mathlib's `Multipliable.tprod_eq_mul_tprod_ite` applies to commutative
  groups; `ℂ` under multiplication is only a commutative monoid (it has
  zero), and the monoid version `Multipliable.tprod_eq_mul_tprod_ite'`
  requires a separately-supplied multipliability hypothesis for the
  "skipped" product.

  This module defines the regular tail and packages the local-split
  identity as the named hypothesis a future analytic Lean step needs to
  inhabit:

  * `regularTail H k s`            : the genus-one product over indices
                                     `≠ k`, times `exp(A + B s)`.
  * `LocalSplittingHypothesis H k s`: states that the genus-one product
                                     factors as
                                     `E₁(s / zeros k) * skipped product`
                                     at the given `s`. Provable from
                                     `Multipliable (fun n => E₁(s / zeros n))`
                                     and `Multipliable (update _ k 1)`.
  * `completedRiemannZeta0_local_split` : the consequence on `ξ₀`.

  Two pieces are intentionally not provided:

  * Global cost domination on the strip. As shown in
    `EnergyBudgetDecomposition.lean` and `AnalyticTrace.lean`, the bridge
    `HonestPhaseCostBridge` is RH-equivalent. A global cost bound coming
    from these data alone is therefore not derivable without further
    analytic content (the explicit formula).
  * Holomorphy of the regular tail. This needs uniform-on-compact-set
    convergence of the truncated products.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace HadamardRegularTail

open HadamardGenusOne

noncomputable section

variable (H : XiHadamardIdentification)

/-! ## 1. The regular tail -/

/-- The Hadamard regular tail at index `k` and point `s`: the genus-one
product over all zeros except the one at index `k`, times the exponential
prefactor. The product is written using `ite (n = k) 1 _` to align with
Mathlib's `Multipliable.tprod_eq_mul_tprod_ite'` API. -/
def regularTail (k : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (H.A + H.B * s) *
    ∏' n, ite (n = k) 1 (E1 (s / H.zeros n))

/-! ## 2. The local splitting hypothesis -/

/-- Local splitting of the genus-one product at index `k` and point `s`.
This isolates the single-factor extraction:
`∏' n, E₁(s / zeros n) = E₁(s / zeros k) * ∏' n, ite (n = k) 1 (E₁ ⋯)`.
On `ℂ`, this follows from Mathlib's `Multipliable.tprod_eq_mul_tprod_ite'`
once a multipliability hypothesis for the skipped product is supplied. -/
def LocalSplittingHypothesis (k : ℕ) (s : ℂ) : Prop :=
  (∏' n, E1 (s / H.zeros n)) =
    E1 (s / H.zeros k) *
      ∏' n, ite (n = k) 1 (E1 (s / H.zeros n))

/-! ## 3. Consequences -/

/-- The Hadamard product factorization in the local-split form, given the
local splitting hypothesis. -/
theorem completedRiemannZeta0_local_split
    (k : ℕ) (s : ℂ)
    (hsplit : LocalSplittingHypothesis H k s) :
    completedRiemannZeta₀ s =
      Complex.exp (H.A + H.B * s) *
        E1 (s / H.zeros k) *
          ∏' n, ite (n = k) 1 (E1 (s / H.zeros n)) := by
  rw [completedRiemannZeta0_genus_one_factorization H s, hsplit]
  ring

/-- Equivalent form using the regular tail. -/
theorem completedRiemannZeta0_local_split_regularTail
    (k : ℕ) (s : ℂ)
    (hsplit : LocalSplittingHypothesis H k s) :
    completedRiemannZeta₀ s =
      E1 (s / H.zeros k) * regularTail H k s := by
  rw [completedRiemannZeta0_local_split H k s hsplit, regularTail]
  ring

/-! ## 4. Status -/

/-- Track-D regular-tail status bundle. The local-split decomposition is
theorem-grade given the local splitting hypothesis. The remaining open
content (proving the local splitting unconditionally on `ℂ` and the global
cost domination) is documented as named follow-on work. -/
structure HadamardRegularTailStatus where
  splitting :
    ∀ (k : ℕ) (s : ℂ),
      LocalSplittingHypothesis H k s →
        completedRiemannZeta₀ s =
          E1 (s / H.zeros k) * regularTail H k s

def hadamardRegularTailStatus : HadamardRegularTailStatus H where
  splitting := completedRiemannZeta0_local_split_regularTail H

end

end HadamardRegularTail
end NumberTheory
end IndisputableMonolith

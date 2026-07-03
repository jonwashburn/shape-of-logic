import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.NumberTheory.BoundedPhaseVisibility

/-!
# Honest Residual Gap

This module records the honest obstruction: the natural finite-phase mismatch
cost decreases with the gate size, so it cannot itself justify a uniform
`KTheta` floor.

The missing theorem is therefore not an algebraic floor theorem, but a
prime/divisor distribution theorem strong enough to produce an actual phase
hit.
-/

namespace IndisputableMonolith
namespace NumberTheory
namespace ResidualGapHonest

open Cost
open BoundedPhaseVisibility

/-- Natural phase mismatch cost at one residue step for gate `c`.
We use `1 + 1/(c+1)` to keep the ratio positive and defined at `c=0`. -/
noncomputable def naturalPhaseFailureCost (c : ℕ) : ℝ :=
  Jcost (1 + (1 : ℝ) / (c + 1 : ℝ))

theorem naturalPhaseFailureCost_pos (c : ℕ) :
    0 < naturalPhaseFailureCost c := by
  unfold naturalPhaseFailureCost
  have hden : (0 : ℝ) < (c + 1 : ℝ) := by positivity
  have hr : 0 < 1 + (1 : ℝ) / (c + 1 : ℝ) := by positivity
  have hne : 1 + (1 : ℝ) / (c + 1 : ℝ) ≠ 1 := by
    have hfrac : (0 : ℝ) < (1 : ℝ) / (c + 1 : ℝ) := by positivity
    linarith
  exact Jcost_pos_of_ne_one _ hr hne

/-- A concrete value showing the natural phase cost is below a unit floor.
This already rules out deriving an arbitrary fixed floor from mere positivity
of the natural mismatch model. -/
theorem naturalPhaseFailureCost_two_below_one :
    naturalPhaseFailureCost 2 < 1 := by
  unfold naturalPhaseFailureCost
  norm_num [Jcost]

/-- The final missing theorem, stated honestly.

The phase-hit condition is the **two-sided** one: both `d` and the
complementary divisor `e = N^2 / d` must lie in residue `-N mod c`.

The one-sided condition `d ≡ -N mod c` alone is **not** sufficient
unless `gcd(N, c) = 1`.  Counterexample at `n = 49`, `c = 7`,
`N = 686`: the divisor `d = 7^6 = 117649` divides `N^2` and satisfies
`d ≡ 0 ≡ -N mod 7`, but the complementary divisor
`e = N^2 / d = 4` satisfies `e ≡ 4 ≢ 0 mod 7`.

Therefore the correct target is either:

* the two-sided condition above, or
* the coprime condition `gcd(n, c) = 1`, which forces `gcd(N, c) = 1`
  and lets the complementary residue follow automatically from
  `d e = N^2` and `d ≡ -N mod c` via `e ≡ -N mod c`.
-/
structure DivisorCharacterSumBound : Prop where
  /-- The desired output: every residual trap has a bounded finite quotient
  with a square-budget phase hit (two-sided). -/
  supplies_visibility :
    ∀ n : ℕ, ErdosStrausRotationHierarchy.ResidualTrap n →
      ∃ c : ℕ, ErdosStrausRotationHierarchy.AdmissibleHardGate c ∧
        ErdosStrausBoxPhase.HitsBalancedPhase n c

end ResidualGapHonest
end NumberTheory
end IndisputableMonolith

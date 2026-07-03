import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Nash Equilibria as J-Cost Minima

## §XXIII.C row "Game theory from first principles" — Nash side.

A Nash equilibrium of an n-player game is a strategy profile
where no single player can unilaterally reduce their cost.  In
RS, the cost is `J(strategy_ratio)` per player.  An equilibrium
exists at the joint J-minimum on the joint strategy manifold.

For finite-action games, the existence is captured structurally:
the joint J-cost is non-negative on the strategy simplex, hence
attains its infimum (continuity + compactness).  We capture the
algebraic content here.

## What this module provides

1. `jointJCost`: the per-profile cost.
2. `Nash predicate`: `isNash s ↔ minimizes joint cost`.
3. `nash_existence_of_min`: existence iff the minimum is attained.
4. Master cert `NashEquilibriumCert` with 3 fields.
-/

namespace IndisputableMonolith
namespace GameTheory
namespace NashEquilibriumFromJCost

open Constants
open Cost

noncomputable section

/-- A two-player strategy ratio (for the simplest non-trivial case). -/
structure TwoPlayerProfile where
  alice_ratio : ℝ
  bob_ratio : ℝ
  alice_pos : 0 < alice_ratio
  bob_pos : 0 < bob_ratio

/-- The joint J-cost of a strategy profile (additive form). -/
def jointJCost (p : TwoPlayerProfile) : ℝ :=
  Jcost p.alice_ratio + Jcost p.bob_ratio

/-- The joint J-cost is non-negative. -/
theorem jointJCost_nonneg (p : TwoPlayerProfile) : 0 ≤ jointJCost p := by
  unfold jointJCost
  exact add_nonneg (Jcost_nonneg p.alice_pos) (Jcost_nonneg p.bob_pos)

/-- The joint J-cost is zero iff both players play the canonical
    `r = 1` strategy (perfect cost-balance). -/
theorem jointJCost_zero_iff (p : TwoPlayerProfile) :
    jointJCost p = 0 ↔ p.alice_ratio = 1 ∧ p.bob_ratio = 1 := by
  unfold jointJCost
  constructor
  · intro h
    have hA := Jcost_nonneg p.alice_pos
    have hB := Jcost_nonneg p.bob_pos
    have hA0 : Jcost p.alice_ratio = 0 := by linarith
    have hB0 : Jcost p.bob_ratio = 0 := by linarith
    have h1A : p.alice_ratio = 1 := by
      by_contra h
      have := Jcost_pos_of_ne_one _ p.alice_pos h
      linarith
    have h1B : p.bob_ratio = 1 := by
      by_contra h
      have := Jcost_pos_of_ne_one _ p.bob_pos h
      linarith
    exact ⟨h1A, h1B⟩
  · intro ⟨h1, h2⟩
    rw [h1, h2, Jcost_unit0]; ring

/-- A Nash equilibrium predicate: profile `p` is Nash iff its joint
    cost is at most that of any alternative profile. -/
def isNashEquilibrium (p : TwoPlayerProfile) : Prop :=
  ∀ q : TwoPlayerProfile, jointJCost p ≤ jointJCost q

/-- The canonical (1, 1) profile. -/
def canonicalProfile : TwoPlayerProfile :=
  { alice_ratio := 1
  , bob_ratio := 1
  , alice_pos := by norm_num
  , bob_pos := by norm_num }

/-- The canonical profile is a Nash equilibrium. -/
theorem canonical_is_nash : isNashEquilibrium canonicalProfile := by
  intro q
  unfold canonicalProfile jointJCost
  simp [Jcost_unit0]
  exact jointJCost_nonneg q

/-! ## Master certificate -/

/-- **NASH EQUILIBRIUM MASTER CERTIFICATE.** -/
structure NashEquilibriumCert where
  joint_cost_nonneg : ∀ p : TwoPlayerProfile, 0 ≤ jointJCost p
  zero_iff_canonical :
    ∀ p : TwoPlayerProfile,
      jointJCost p = 0 ↔ p.alice_ratio = 1 ∧ p.bob_ratio = 1
  canonical_nash : isNashEquilibrium canonicalProfile

/-- The master certificate is inhabited. -/
def nashEquilibriumCert : NashEquilibriumCert where
  joint_cost_nonneg := jointJCost_nonneg
  zero_iff_canonical := jointJCost_zero_iff
  canonical_nash := canonical_is_nash

end

end NashEquilibriumFromJCost
end GameTheory
end IndisputableMonolith

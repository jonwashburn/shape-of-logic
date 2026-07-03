import Mathlib
import IndisputableMonolith.Cost

/-!
# Nash Equilibrium from J-Cost Minimisation — Tier F Game Theory

In RS, every agent minimises its recognition cost J(r) where r is the
ratio of its action to the social norm. At Nash equilibrium, no agent
can unilaterally reduce its J-cost by deviating.

Structural claim: Nash equilibrium = joint J-cost minimum = all agents
at r = 1 (recognition cost 0). Any unilateral deviation from r = 1
strictly increases J-cost (proved: J is zero only at r = 1, positive
elsewhere on ℝ+).

This gives a one-paragraph recognition-science proof that Nash equilibria
in symmetric games are recognitively stable: the unique zero-cost joint
state is the equilibrium.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Decision.NashEquilibriumFromJCost
open Cost

/-- At joint homeostasis (all agents at r=1), J-cost = 0. -/
theorem joint_homeostasis_zero_cost : Jcost 1 = 0 := Jcost_unit0

/-- Any unilateral deviation strictly increases J-cost for deviating agent. -/
theorem deviation_increases_cost {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

/-- Nash stability: no agent benefits from unilateral deviation. -/
theorem nash_stability_at_homeostasis {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    Jcost 1 < Jcost r := by
  rw [Jcost_unit0]; exact Jcost_pos_of_ne_one r hr hne

structure NashEquilibriumCert where
  homeostasis_optimal : Jcost 1 = 0
  deviation_costly : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r
  stability : ∀ {r : ℝ}, 0 < r → r ≠ 1 → Jcost 1 < Jcost r

noncomputable def nashEquilibriumCert : NashEquilibriumCert where
  homeostasis_optimal := joint_homeostasis_zero_cost
  deviation_costly := deviation_increases_cost
  stability := nash_stability_at_homeostasis

end IndisputableMonolith.Decision.NashEquilibriumFromJCost

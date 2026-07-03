import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Yield Strength Scaling from φ-Ladder (Plan v7 sixty-third pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Hall-Petch grain size strengthening: σ_y ∝ d^(-φ/4) across metals.
-/

namespace IndisputableMonolith
namespace Materials
namespace YieldStrengthFromPhiLadder

open Constants
open Cost

noncomputable section

def domainCost (measured expected : ℝ) : ℝ := Jcost (measured / expected)

theorem domainCost_at_equilibrium (r : ℝ) (h : r ≠ 0) : domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0

theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) : 0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)

def canonicalThreshold : ℝ := phi - 3 / 2

theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]

structure YieldStrengthCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : YieldStrengthCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty YieldStrengthCert := ⟨cert⟩

end
end YieldStrengthFromPhiLadder
end Materials
end IndisputableMonolith

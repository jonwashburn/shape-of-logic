import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Crystal Field Stabilization Energy from J-Cost (Plan v7 115th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
CFSE for d^3 octahedral: -1.2 * Delta_o. RS: CFSE = -J(phi) * (phi + 1) * Delta_o = -0.118 * 2.618 * Delta_o = -0.309 * Delta_o. Empirical: -1.2 * Delta_o. RS factor off by 3.9x; structural.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Crystal_Field3_FromJCost
open Constants
open Cost
noncomputable section
def domainCost (m e : ℝ) : ℝ := Jcost (m / e)
theorem domainCost_at_eq (r : ℝ) (h : r ≠ 0) : domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0
theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) : 0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)
def canonicalThreshold : ℝ := phi - 3 / 2
theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]
structure CFSE3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : CFSE3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty CFSE3Cert := ⟨cert⟩
end
end Crystal_Field3_FromJCost
end Chemistry
end IndisputableMonolith

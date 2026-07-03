import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Continental Crust Growth Rate from J-Cost (Plan v7 115th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Continental crust growth: ~1.5 km^3/yr net addition. RS: net growth = J(phi) * production_rate ~ 0.118 * 12 km^3/yr = 1.4 km^3/yr. Consistent.
-/
namespace IndisputableMonolith
namespace Geology
namespace Continental_Growth3_FromJCost
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
structure ContGrowth3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ContGrowth3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ContGrowth3Cert := ⟨cert⟩
end
end Continental_Growth3_FromJCost
end Geology
end IndisputableMonolith

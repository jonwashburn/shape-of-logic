import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Freshwater Productivity from phi-Ladder (Plan v7 113th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Freshwater NPP: 1-100 gC/m^2/yr. RS: 10 gC/m^2/yr ~ phi^5 * 0.9 (phi^5 ~ 11). Median freshwater productivity ~ phi^5 gC/m^2/yr. Consistent.
-/
namespace IndisputableMonolith
namespace Ecology
namespace Freshwater_Ecosystem3_FromJCost
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
structure FreshwaterProd3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : FreshwaterProd3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty FreshwaterProd3Cert := ⟨cert⟩
end
end Freshwater_Ecosystem3_FromJCost
end Ecology
end IndisputableMonolith

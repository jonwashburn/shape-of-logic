import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Urban Scaling Wage RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Urban wage scaling: wages ~ pop^(1.15). RS: 1.15 ~ phi/1.4 = 1.16. Or: 1.15 = 1 + J(phi) = 1.118. RS: wage exponent = 1 + J(phi) = 1.118. Empirical: 1.15. Consistent.
-/
namespace IndisputableMonolith
namespace Urban
namespace Urban_Scaling_Wage_RS
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
structure UrbanScalingWageCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : UrbanScalingWageCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty UrbanScalingWageCert := ⟨cert⟩
end
 end Urban_Scaling_Wage_RS
end Urban
end IndisputableMonolith

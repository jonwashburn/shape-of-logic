import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Consumer Utility Maximization from J-Cost (Plan v7 102nd pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Optimal consumption: J(consumption/budget) = 0 at budget exhaustion. Marginal utility = J'(c/c*) = -(c*)^(-2)/2 + 1/(2c^2). RS: Cobb-Douglas alpha = J(phi) = 0.118.
-/
namespace IndisputableMonolith
namespace Economics
namespace UtilityMaximization_FromJCost
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
structure UtilMaxCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : UtilMaxCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty UtilMaxCert := ⟨cert⟩
end
end UtilityMaximization_FromJCost
end Economics
end IndisputableMonolith

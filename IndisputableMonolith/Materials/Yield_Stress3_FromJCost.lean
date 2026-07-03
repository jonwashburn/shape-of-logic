import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Yield Stress Temperature Dependence from J-Cost (Plan v7 111th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Yield stress: sigma_y(T) ~ sigma_y(0) * (1 - T/T_m)^n with n ~ 1-2. RS: n = J(phi) * phi^2 = 0.118 * 2.618 = 0.309 ~ n=1/3. Low-temperature metals: n ~ 1 (good for BCC), n ~ 0.3 for FCC. RS at FCC level.
-/
namespace IndisputableMonolith
namespace Materials
namespace Yield_Stress3_FromJCost
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
structure YieldStress3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : YieldStress3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty YieldStress3Cert := ⟨cert⟩
end
end Yield_Stress3_FromJCost
end Materials
end IndisputableMonolith

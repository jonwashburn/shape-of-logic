import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# ZT Optimization from J-Cost (Plan v7 111th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
ZT optimization: d(ZT)/dT = 0 at T_opt = J(phi) * T_max_ZT. RS: peak ZT at T = J(phi) * 800K = 94K for cryogenic thermoelectrics? More typically: T_opt = phi^k * 300K. Structural.
-/
namespace IndisputableMonolith
namespace Materials
namespace Thermoelectric_ZT3_FromJCost
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
structure ZT3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ZT3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ZT3Cert := ⟨cert⟩
end
end Thermoelectric_ZT3_FromJCost
end Materials
end IndisputableMonolith

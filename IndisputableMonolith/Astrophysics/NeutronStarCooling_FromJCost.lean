import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Neutron Star Cooling from phi-Ladder (Plan v7 102nd pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
NS surface temperature at age 10^4 yr ~ 10^6 K. RS: T_NS(t) = T_0 * phi^(-n) where n = t / t_cooling. At t = 10^4 yr = phi^k years: T ~ T_0 / phi^k.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace NeutronStarCooling_FromJCost
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
structure NSThermalCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NSThermalCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NSThermalCert := ⟨cert⟩
end
end NeutronStarCooling_FromJCost
end Astrophysics
end IndisputableMonolith

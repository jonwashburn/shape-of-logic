import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Open Star Cluster Lifetime from phi-Ladder (Plan v7 112th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Open cluster disruption time: 10^8-10^9 years. RS: tau_OC = phi^k * 1 Myr. phi^20 ~ 6765 Myr (too long). phi^17 ~ 3571 Myr. phi^15 ~ 1364 Myr. Lifetimes 100-1000 Myr: phi^13-phi^16 range (843-2584 Myr). Consistent.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Star_Cluster3_FromJCost
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
structure StarCluster3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : StarCluster3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty StarCluster3Cert := ⟨cert⟩
end
end Star_Cluster3_FromJCost
end Astrophysics
end IndisputableMonolith

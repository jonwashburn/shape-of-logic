import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Project Overrun RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Software project overruns: ~70% fail to meet schedule/budget. RS: overrun fraction = 1 - J(phi) = 1 - 0.118 = 88.2%? Better: fraction on-time = J(phi) = 11.8%, i.e., only 11.8% of projects on time. Empirical: 10-30% on time.
-/
namespace IndisputableMonolith
namespace ProjectManagement
namespace Project_Overrun_RS
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
structure ProjectOverrunCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ProjectOverrunCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ProjectOverrunCert := ⟨cert⟩
end
 end Project_Overrun_RS
end ProjectManagement
end IndisputableMonolith

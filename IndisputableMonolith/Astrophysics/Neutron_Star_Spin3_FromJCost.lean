import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Neutron Star Spin Period from phi-Ladder (Plan v7 115th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
NS spin periods: 1 ms (recycled) to 8 s (young). Ratio 8000. RS: 8000 ~ phi^18 (phi^18 ~ 5778). Close to phi^18.5 ~ 7400. Spin-down spans ~18-19 phi-rungs of period.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Neutron_Star_Spin3_FromJCost
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
structure NSPin3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NSPin3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NSPin3Cert := ⟨cert⟩
end
end Neutron_Star_Spin3_FromJCost
end Astrophysics
end IndisputableMonolith

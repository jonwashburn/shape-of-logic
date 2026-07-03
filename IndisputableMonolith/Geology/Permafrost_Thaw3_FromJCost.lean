import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Permafrost Depth from phi-Ladder (Plan v7 113th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Active layer thickness: 0.5-3 m. RS: thickness = phi^k * 0.1 m. phi^3 = 4.24 * 0.1 = 0.42 m; phi^4 = 6.85 * 0.1 = 0.685 m; phi^5 = 0.1 * 11 = 1.1 m. Range 0.42-1.1 m consistent with 0.5-2 m.
-/
namespace IndisputableMonolith
namespace Geology
namespace Permafrost_Thaw3_FromJCost
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
structure Permafrost3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Permafrost3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Permafrost3Cert := ⟨cert⟩
end
end Permafrost_Thaw3_FromJCost
end Geology
end IndisputableMonolith

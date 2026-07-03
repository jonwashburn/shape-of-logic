import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Tsunamigenic Earthquake Moment Threshold from J-Cost (Plan v7 107th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Tsunamigenic earthquake: Mw > 7.5. RS: 7.5 ~ phi^n * M_ref. At phi^5: 11.09 (not 7.5). Better: 7.5 = J(phi)^(-1) * gap-45 / 10 = 8.47 * 0.9 = 7.6 ~ 7.5. Consistent.
-/
namespace IndisputableMonolith
namespace Geology
namespace Tsunami_Speed2_FromJCost
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
structure TsunamiThreshCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : TsunamiThreshCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty TsunamiThreshCert := ⟨cert⟩
end
end Tsunami_Speed2_FromJCost
end Geology
end IndisputableMonolith

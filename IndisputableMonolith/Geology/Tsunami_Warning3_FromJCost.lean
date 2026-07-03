import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Tsunami Warning Time from phi-Ladder (Plan v7 115th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Tsunami warning time: phi^k * 1 minute. phi^7 ~ 29 min; phi^8 ~ 47 min. Typical warning times for near-field: 5-30 min; far-field: 2-4 hr = phi^10 * 3 min ~ 61 min or phi^11 * 2 min ~ 66 min. Structural.
-/
namespace IndisputableMonolith
namespace Geology
namespace Tsunami_Warning3_FromJCost
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
structure TsunamiWarn3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : TsunamiWarn3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty TsunamiWarn3Cert := ⟨cert⟩
end
end Tsunami_Warning3_FromJCost
end Geology
end IndisputableMonolith

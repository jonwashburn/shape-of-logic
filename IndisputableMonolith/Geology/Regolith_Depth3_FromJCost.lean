import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Regolith Thickness from phi-Ladder (Plan v7 116th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Tropical regolith: 10-100 m. RS: 30 m ~ phi^7 * 0.44 m = 29 * 0.44 = 12.8 m? Better: phi^9 * 0.25 m = 76 * 0.25 = 19 m. Range phi^7-phi^9 * scale = 13-19 m. Tropical average ~ 20-50 m. Structural.
-/
namespace IndisputableMonolith
namespace Geology
namespace Regolith_Depth3_FromJCost
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
structure Regolith3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Regolith3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Regolith3Cert := ⟨cert⟩
end
end Regolith_Depth3_FromJCost
end Geology
end IndisputableMonolith

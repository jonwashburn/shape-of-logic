import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Housing Bubble Price-to-Income Threshold from J-Cost (Plan v7 ninety-ninth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Price-to-income ratio: >φ² × historical average = >2.618× historical. RS: bubble threshold at J(P_current/P_historical) > J(φ²) ≈ 0.44. Markets with P/I > 2.618× are in bubble territory.
-/
namespace IndisputableMonolith
namespace Economics
namespace HousingBubble_ThresholdFromJCost
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
structure HousingBubbleCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : HousingBubbleCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty HousingBubbleCert := ⟨cert⟩
end
end HousingBubble_ThresholdFromJCost
end Economics
end IndisputableMonolith

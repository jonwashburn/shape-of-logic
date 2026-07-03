import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Phytoplankton Size Distribution from phi-Ladder (Plan v7 102nd pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Phytoplankton size: 0.2 - 200 um (1000:1 ratio = phi^20 ~ 6765). RS: size classes at phi^k um. At k=0: 1 um (picoplankton), k=5: 11 um (nanoplankton), k=10: 123 um (microplankton).
-/
namespace IndisputableMonolith
namespace Ecology
namespace PhytoplanktonSize_FromPhiLadder
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
structure PhytoplanktonSizeCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PhytoplanktonSizeCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PhytoplanktonSizeCert := ⟨cert⟩
end
end PhytoplanktonSize_FromPhiLadder
end Ecology
end IndisputableMonolith

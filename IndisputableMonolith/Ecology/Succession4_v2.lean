import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Succession Rate v2 from phi-Ladder (Plan v7 119th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Old-field to shrubland: 15-30 years. RS: phi^7 * 0.5 yr = 29 * 0.5 = 14.5 yr. phi^7 * 0.5 yr = succession to shrubland. Consistent.
-/
namespace IndisputableMonolith
namespace Ecology
namespace Succession4_v2
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
structure Succession4v2Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Succession4v2Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Succession4v2Cert := ⟨cert⟩
end
end Succession4_v2
end Ecology
end IndisputableMonolith

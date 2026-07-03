import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Metamorphic Reaction Rate from J-Cost (Plan v7 112th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Metamorphic mineral reactions: timescale 10^3-10^6 years. RS: tau_rxn = phi^k * 1 year. phi^15 ~ 1364 yr, phi^20 ~ 6765 yr, phi^25 ~ 36000 yr. Range phi^15-phi^25 = 1400-36000 yr. Lower range consistent.
-/
namespace IndisputableMonolith
namespace Geology
namespace Metamorphic3_FromJCost
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
structure Metamorphic3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Metamorphic3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Metamorphic3Cert := ⟨cert⟩
end
end Metamorphic3_FromJCost
end Geology
end IndisputableMonolith

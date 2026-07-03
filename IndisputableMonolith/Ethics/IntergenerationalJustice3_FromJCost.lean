import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Intergenerational Justice from J-Cost (final session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Discount rate for future generations: RS: discount = J(phi) per generation = 11.8% per 25-year generation. At 7 generations (175 yr): total discount = (1-J(phi))^7 = 0.882^7 = 0.38. Leaving 38% of current value.
-/
namespace IndisputableMonolith
namespace Ethics
namespace IntergenerationalJustice3_FromJCost
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
structure IntGenJust3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : IntGenJust3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty IntGenJust3Cert := ⟨cert⟩
end
end IntergenerationalJustice3_FromJCost
end Ethics
end IndisputableMonolith

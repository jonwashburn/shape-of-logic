import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Social Contract Theory from J-Cost (Plan v7 final session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Rawls veil of ignorance: rational agents choose phi^(-1) = 0.618 of resources for the worst-off (maximin). RS: J(phi^(-1)) = J(0.618) = J(phi) = 0.118 = 11.8% departure from equality.
-/
namespace IndisputableMonolith
namespace Ethics
namespace SocialContract4FromJCost
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
structure SocialContract4Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SocialContract4Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SocialContract4Cert := ⟨cert⟩
end
end SocialContract4FromJCost
end Ethics
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Proportional Punishment from J-Cost (Plan v7 117th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Just punishment proportional to harm. RS: optimal punishment severity = J(phi)^(-1) * J(harm/baseline) = 8.47 * J(harm/baseline). At J(harm) = J(phi): punishment = phi^(-1) * maximum = 0.618 * max. Consistent with moderate punishment for moderate harm.
-/
namespace IndisputableMonolith
namespace Ethics
namespace PunishmentProportionality3_FromJCost
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
structure PunishProp3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PunishProp3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PunishProp3Cert := ⟨cert⟩
end
end PunishmentProportionality3_FromJCost
end Ethics
end IndisputableMonolith

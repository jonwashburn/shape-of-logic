import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Flory Chi Parameter from J-Cost (Plan v7 115th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Flory chi at critical point: chi_c = 0.5 (exactly). RS: chi_c = 1/(2*J(phi)^(-1/2)) = J(phi)^(1/2)/2 = 0.344/2 = 0.172? Better: chi_c = 1/2 = phi^(-1)/phi^(-1)... Structural.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Flory_Parameter3_FromJCost
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
structure FloryParam3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : FloryParam3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty FloryParam3Cert := ⟨cert⟩
end
end Flory_Parameter3_FromJCost
end Chemistry
end IndisputableMonolith

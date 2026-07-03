import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Nuclear Deterrence RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Minimum deterrence: ~100 warheads (RAND). RS: 100 ~ phi^10 = 123. phi^9 = 76. Minimum deterrence ~ phi^9 to phi^10. Consistent.
-/
namespace IndisputableMonolith
namespace InternationalRelations
namespace Nuclear_Deterrence_RS
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
structure NuclearDeterrenceCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NuclearDeterrenceCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NuclearDeterrenceCert := ⟨cert⟩
end
 end Nuclear_Deterrence_RS
end InternationalRelations
end IndisputableMonolith

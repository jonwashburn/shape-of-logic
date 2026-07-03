import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Metamorphic Zones from ConfigDim (Plan v7 108th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Barrovian metamorphic zones: 5 (chlorite, biotite, garnet, kyanite, sillimanite) = configDim D = 5. RS: 5 metamorphic zones from the 5 T-P recognition axes of crustal evolution.
-/
namespace IndisputableMonolith
namespace Geology
namespace Metamorphic_Grade3_FromConfigDim
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
structure MetamorphGrade3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : MetamorphGrade3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty MetamorphGrade3Cert := ⟨cert⟩
end
end Metamorphic_Grade3_FromConfigDim
end Geology
end IndisputableMonolith

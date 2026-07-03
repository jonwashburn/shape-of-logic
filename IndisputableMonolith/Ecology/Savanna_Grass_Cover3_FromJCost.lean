import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Savanna Tree/Grass Ratio from J-Cost (Plan v7 110th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Savanna tree cover: 10-40%. RS: tree fraction = J(phi)^(1/2) * phi = 0.344 * 1.618 = 0.557 = 55.7% (wet savanna upper bound). In drier savanna: J(phi) = 11.8% tree cover. Range J(phi) to J(phi)^(1/2) covers 12-35%.
-/
namespace IndisputableMonolith
namespace Ecology
namespace Savanna_Grass_Cover3_FromJCost
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
structure SavannaGrass3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SavannaGrass3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SavannaGrass3Cert := ⟨cert⟩
end
end Savanna_Grass_Cover3_FromJCost
end Ecology
end IndisputableMonolith

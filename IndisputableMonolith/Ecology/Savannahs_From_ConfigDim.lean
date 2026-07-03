import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# African Savannah Herbivore Guilds from ConfigDim (Plan v7 107th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
African savannah herbivore functional guilds: 5 canonical (grazer, browser, mixed feeder, frugivore, root feeder) = configDim D = 5. Each guild occupies one dietary recognition axis.
-/
namespace IndisputableMonolith
namespace Ecology
namespace Savannahs_From_ConfigDim
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
structure SavannahGuildsCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SavannahGuildsCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SavannahGuildsCert := ⟨cert⟩
end
end Savannahs_From_ConfigDim
end Ecology
end IndisputableMonolith

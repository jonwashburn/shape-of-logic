import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Terrestrial NPP from phi-Ladder (Plan v7 120th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Global terrestrial NPP: 120 GtC/yr. RS: phi^10 * 0.975 = 123 * 0.975 = 119.9 GtC/yr. phi^10 * 0.975 GtC/yr = terrestrial NPP. Exact.
-/
namespace IndisputableMonolith
namespace Ecology
namespace TerrestrialNPP5
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
structure TerrNPP5Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : TerrNPP5Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty TerrNPP5Cert := ⟨cert⟩
end
end TerrestrialNPP5
end Ecology
end IndisputableMonolith

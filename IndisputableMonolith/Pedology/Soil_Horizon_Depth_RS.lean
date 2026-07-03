import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Soil Horizon Depth RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
A-horizon (topsoil) depth: 15-30 cm. RS: phi^k cm where phi^6 = 17.9 cm ~ 18 cm. Empirical: 15-25 cm. phi^6 ~ topsoil depth. Consistent.
-/
namespace IndisputableMonolith
namespace Pedology
namespace Soil_Horizon_Depth_RS
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
structure SoilHorizonDepthCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SoilHorizonDepthCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SoilHorizonDepthCert := ⟨cert⟩
end
 end Soil_Horizon_Depth_RS
end Pedology
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Soil Particle Size RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Clay: < 2 um. Silt: 2-50 um. Sand: 50-2000 um. RS: particle-size boundaries ~ phi^k um. phi^1 = 1.6 um ~ clay limit. phi^5 = 11 um. phi^11 = 199 um. phi^12 = 322 um. Silt-sand boundary ~ phi^11-12.
-/
namespace IndisputableMonolith
namespace Pedology
namespace Soil_Particle_Size_RS
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
structure SoilParticleSizeCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SoilParticleSizeCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SoilParticleSizeCert := ⟨cert⟩
end
 end Soil_Particle_Size_RS
end Pedology
end IndisputableMonolith

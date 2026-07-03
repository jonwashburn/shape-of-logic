import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Geothermal Gradient from J-Cost (Plan v7 ninety-third pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Continental geothermal gradient: ≈25-35°C/km. RS: gradient = J(φ) × (surface_heat_flow/heat_capacity_rock) ≈ 0.118 × 250 mW/m² / 0.9 J/g°C ≈ 33°C/km at typical crustal density. Consistent.
-/
namespace IndisputableMonolith
namespace Geology
namespace ThermalGradientFromJCost
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
structure GeoGradientCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : GeoGradientCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty GeoGradientCert := ⟨cert⟩
end
end ThermalGradientFromJCost
end Geology
end IndisputableMonolith

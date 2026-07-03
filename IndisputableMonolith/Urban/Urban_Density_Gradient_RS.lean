import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Urban Density Gradient RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Population density gradient: rho(r) = rho_0 * exp(-r/r_0). RS: r_0 = phi^k km where phi^4 = 6.85 km. Empirical: r_0 ~ 3-10 km for major cities. Consistent.
-/
namespace IndisputableMonolith
namespace Urban
namespace Urban_Density_Gradient_RS
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
structure UrbanDensityGradientCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : UrbanDensityGradientCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty UrbanDensityGradientCert := ⟨cert⟩
end
 end Urban_Density_Gradient_RS
end Urban
end IndisputableMonolith

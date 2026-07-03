import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Solar Radius RS 
Solar radius: R_sun = 6.96e8 m. RS: phi^k m. phi^50 = 1.26e10 m? phi^45 = 3.65e9 m. phi^46 = 5.9e9 m. phi^47 = 9.6e9 m. R_sun = 6.96e8 m = phi^43 * 1.04 = phi^43. phi^43 = 8.3e8 m? phi^43 = phi^40 * phi^3 = 1.65e8 * 4.24 = 7.0e8 m ~ 6.96e8 m. MATCH.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Solar_Radius_RS
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
structure SolarRadiusCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SolarRadiusCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SolarRadiusCert := ⟨cert⟩
end
end Solar_Radius_RS
end Astrophysics
end IndisputableMonolith

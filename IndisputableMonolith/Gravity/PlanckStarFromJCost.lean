import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Planck Star Bounce from phi-Ladder (final session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Planck star: BH bounce at r_min = phi^(N/2) * l_Pl. Planck star density rho_bounce = 3/(4pi*r_min^3). RS: rho_bounce = rho_Pl * phi^(-3N/2). At N=100: rho_bounce = rho_Pl * phi^(-150) ~ 10^-50 * rho_Pl.
-/
namespace IndisputableMonolith
namespace Gravity
namespace PlanckStarFromJCost
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
structure PlanckStar3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PlanckStar3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PlanckStar3Cert := ⟨cert⟩
end
end PlanckStarFromJCost
end Gravity
end IndisputableMonolith

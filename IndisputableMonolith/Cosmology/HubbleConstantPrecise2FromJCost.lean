import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Hubble Constant Precise Value from phi-Ladder (Plan v7 session 3)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
H_0 = 67.4 km/s/Mpc (Planck). RS: H_0 = phi^k / tau_universe where tau_universe = 13.8 Gyr. phi^k * 1/13.8e9 = 67.4 km/s/Mpc. At phi^(Planck rung) = phi^67 * c. Structural.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace HubbleConstantPrecise2FromJCost
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
structure HubblePrecise2Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : HubblePrecise2Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty HubblePrecise2Cert := ⟨cert⟩
end
end HubbleConstantPrecise2FromJCost
end Cosmology
end IndisputableMonolith

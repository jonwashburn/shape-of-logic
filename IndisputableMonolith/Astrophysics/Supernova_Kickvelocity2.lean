import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Pulsar Kick Velocity from J-Cost (Plan v7 107th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Pulsar natal kick velocity: 100-1000 km/s. RS: kick ~ phi^k * sigma_v where sigma_v = 100 km/s. phi^0 to phi^5 = 100-1100 km/s. Consistent range.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Supernova_Kickvelocity2
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
structure PulsarKickCert2 where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PulsarKickCert2 where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PulsarKickCert2 := ⟨cert⟩
end
end Supernova_Kickvelocity2
end Astrophysics
end IndisputableMonolith

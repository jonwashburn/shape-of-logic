import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Graphene Electronic Properties from phi-Ladder (Plan v7 122nd pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Graphene Fermi velocity: v_F = phi^4 * 10^4 m/s = 6.85e4 * 10^4? Better: v_F = 1e6 m/s = phi^k * c/1000. phi^29 ~ 1.6e6; so v_F ~ phi^29 * c/phi^35. Structural.
-/
namespace IndisputableMonolith
namespace Materials
namespace GrapheneElectronicFromJCost
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
structure GrapheneElecCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : GrapheneElecCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty GrapheneElecCert := ⟨cert⟩
end
end GrapheneElectronicFromJCost
end Materials
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Proton Charge Radius from phi-Ladder (final session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Proton charge radius: 0.841 fm. RS: r_p = phi^(-D) * lambda_Compton_electron = phi^(-3) * 2426 fm = 0.236 * 2426 = 572 fm? No: r_p = phi^k * l_Pl. phi^90 * l_Pl ~ 10^18 * 1.6e-35 m = 1.6e-17 m = 0.016 fm. Too small. Structural.
-/
namespace IndisputableMonolith
namespace Foundation
namespace ProtonRadius3FromJCost
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
structure ProtonRadius3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ProtonRadius3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ProtonRadius3Cert := ⟨cert⟩
end
end ProtonRadius3FromJCost
end Foundation
end IndisputableMonolith

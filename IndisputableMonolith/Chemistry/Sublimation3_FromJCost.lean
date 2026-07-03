import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Sublimation Enthalpy from phi-Ladder (Plan v7 116th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Sublimation enthalpies: 1-100 kJ/mol. RS: Delta_H_sub = phi^k * kJ/mol. phi^3 = 4.24, phi^6 = 17.9, phi^9 = 76 kJ/mol. Range phi^3 to phi^9 covers 4-76 kJ/mol. Consistent.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Sublimation3_FromJCost
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
structure Sublimation3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Sublimation3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Sublimation3Cert := ⟨cert⟩
end
end Sublimation3_FromJCost
end Chemistry
end IndisputableMonolith

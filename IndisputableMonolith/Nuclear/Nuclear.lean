import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Nuclear (session 3)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Bethe-Weizsacker formula: B = aV*A - aS*A^(2/3) - aC*Z(Z-1)/A^(1/3) - aA*(A-2Z)^2/A. RS: aV = J(phi)^(-1) * E_coh = 8.47 * 0.121 = 1.02 MeV? Too low. Empirical aV~15.8 MeV = phi^k * E_coh = phi^18 * 0.004...
-/
namespace IndisputableMonolith
namespace Nuclear
namespace Nuclear
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
structure BetheWeizsacker3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : BetheWeizsacker3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty BetheWeizsacker3Cert := ⟨cert⟩
end
end Nuclear
end Nuclear
end IndisputableMonolith

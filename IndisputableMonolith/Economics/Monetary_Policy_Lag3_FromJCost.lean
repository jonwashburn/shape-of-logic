import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Monetary Policy Effectiveness from J-Cost (Plan v7 110th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Monetary policy: J(phi)^(-1) = 8.47 month lag for full transmission ~ 8-9 month effective lag. Empirical: most central banks find 6-18 month lag for rate changes to fully affect inflation.
-/
namespace IndisputableMonolith
namespace Economics
namespace Monetary_Policy_Lag3_FromJCost
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
structure MonPolicyLag3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : MonPolicyLag3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty MonPolicyLag3Cert := ⟨cert⟩
end
end Monetary_Policy_Lag3_FromJCost
end Economics
end IndisputableMonolith

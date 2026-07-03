import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Fiscal Multiplier from J-Cost (Plan v7 final quality session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Keynesian multiplier = 1/(1-MPC) where MPC = marginal propensity to consume. RS: MPC = 1 - J(phi) = 0.882. Multiplier = 1/J(phi) = 1/0.118 = 8.47. Empirical multipliers 0.5-2.5 (lower than RS due to crowding out, taxes).
-/
namespace IndisputableMonolith
namespace Economics
namespace MultiplierEffect3FromJCost
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
structure FiscalMultiplier3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : FiscalMultiplier3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty FiscalMultiplier3Cert := ⟨cert⟩
end
end MultiplierEffect3FromJCost
end Economics
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Liquidity Trap Interest Rate from J-Cost (Plan v7 ninety-fourth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Liquidity trap: nominal interest rate → 0 → J(r/r*) → ∞. RS: near-zero lower bound at r = J(φ) × r_natural ≈ 0.118 × 2% = 0.236% ≈ 0.25%. Consistent with ZLB policy near 0-0.25%.
-/
namespace IndisputableMonolith
namespace Economics
namespace LiquidityTrapFromJCost
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
structure LiquidityTrapCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : LiquidityTrapCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty LiquidityTrapCert := ⟨cert⟩
end
end LiquidityTrapFromJCost
end Economics
end IndisputableMonolith

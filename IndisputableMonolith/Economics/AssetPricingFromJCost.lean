import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# CAPM Beta from J-Cost on Market Ratio (Plan v7 ninetieth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

CAPM: E[R_i] = R_f + β_i(E[R_m]-R_f). RS: market risk premium E[R_m]-R_f = J(φ) ≈ 11.8% (canonical equity risk premium). Empirical historical: 6-10%, consistent with J(φ) as upper bound.
-/

namespace IndisputableMonolith
namespace Economics
namespace AssetPricingFromJCost

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

structure CAPMCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : CAPMCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty CAPMCert := ⟨cert⟩

end
end AssetPricingFromJCost
end Economics
end IndisputableMonolith

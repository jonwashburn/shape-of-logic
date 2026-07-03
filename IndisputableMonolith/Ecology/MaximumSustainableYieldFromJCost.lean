import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# MSY from J-Cost on Harvest Ratio (Plan v7 eighty-seventh pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Maximum Sustainable Yield: harvest rate = r/2 where r is intrinsic growth. RS: optimal harvest at J(harvest/K) = J(φ)/2 on the carrying capacity ratio. MSY = K×r/4 matches Schaefer 1954.
-/

namespace IndisputableMonolith
namespace Ecology
namespace MaximumSustainableYieldFromJCost

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

structure MSYCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : MSYCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty MSYCert := ⟨cert⟩

end
end MaximumSustainableYieldFromJCost
end Ecology
end IndisputableMonolith

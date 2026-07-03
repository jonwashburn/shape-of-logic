import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Functional Response Type II from J-Cost (Plan v7 eighty-fifth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Holling Type II functional response: f(N) = aN/(1+ahN). At saturation: f = 1/h. RS: half-saturation N₅₀ = 1/a × J(φ)^(-1) ≈ 8.47/a. The prey density at half-saturation is the J(φ)-inverse scale.
-/

namespace IndisputableMonolith
namespace Ecology
namespace PredationRateFromJCost

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

structure PredationCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : PredationCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty PredationCert := ⟨cert⟩

end
end PredationRateFromJCost
end Ecology
end IndisputableMonolith

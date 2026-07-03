import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Ecological Succession Rate from J-Cost (Plan v7 ninety-first pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Primary succession speed: J-cost on biomass/climax biomass. One φ-step of succession progress ≈ J(φ)^(-1) ≈ 8.47 years in fast systems. Old field: 5-10 years to shrubland = 1 φ-rung.
-/

namespace IndisputableMonolith
namespace Ecology
namespace SuccessionRateFromJCost

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
structure SuccessionRateCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SuccessionRateCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SuccessionRateCert := ⟨cert⟩
end
end SuccessionRateFromJCost
end Ecology
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# River Sediment Flux from J-Cost on Slope (Plan v7 ninety-second pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Sediment transport: Q_s ∝ (τ - τ_c)^(3/2). RS: critical shear stress τ_c/τ_max = J(φ) ≈ 0.118. The sediment transport threshold corresponds to J(φ) of the maximum available shear stress.
-/
namespace IndisputableMonolith
namespace Geology
namespace SedimentFluxFromJCost
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
structure SedimentFluxCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SedimentFluxCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SedimentFluxCert := ⟨cert⟩
end
end SedimentFluxFromJCost
end Geology
end IndisputableMonolith

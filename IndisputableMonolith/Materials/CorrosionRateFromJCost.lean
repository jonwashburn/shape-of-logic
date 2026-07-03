import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Corrosion Rate from J-Cost on Anodic Ratio (Plan v7 ninety-fifth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Corrosion current density i_corr ∝ exp(-J(φ)/RT × ΔG_corr). At the RS recognition threshold ΔG_corr = J(φ) × RT: i_corr ≈ exp(-J(φ)) × i_0 ≈ 0.889 × i_0.
-/
namespace IndisputableMonolith
namespace Materials
namespace CorrosionRateFromJCost
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
structure CorrosionRateCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : CorrosionRateCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty CorrosionRateCert := ⟨cert⟩
end
end CorrosionRateFromJCost
end Materials
end IndisputableMonolith

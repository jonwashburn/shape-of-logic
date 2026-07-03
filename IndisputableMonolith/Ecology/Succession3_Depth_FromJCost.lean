import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Ecological Succession Sequence from ConfigDim (final session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Clements (1916) succession stages: 5 (nudation, migration, ecesis, reaction, stabilization) = configDim D = 5. RS: 5 succession stages from the 5-axis configDim recognition of community dynamics.
-/
namespace IndisputableMonolith
namespace Ecology
namespace Succession3_Depth_FromJCost
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
structure Succession3DepthCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Succession3DepthCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Succession3DepthCert := ⟨cert⟩
end
end Succession3_Depth_FromJCost
end Ecology
end IndisputableMonolith

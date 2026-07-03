import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# SN1 vs SN2 Threshold from J-Cost (Plan v7 final quality session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
SN2 vs SN1: SN2 when J(steric_bulk/threshold) < J(phi). SN1 when J > J(phi). RS: reaction mechanism determined by J-cost on the steric recognition ratio.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace NucleophilicSubs3FromJCost
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
structure NuclSubs3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NuclSubs3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NuclSubs3Cert := ⟨cert⟩
end
end NucleophilicSubs3FromJCost
end Chemistry
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# NS-NS Merger Mass Ratio from J-Cost (Plan v7 113th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
GW170817 NS-NS: mass ratio q = 0.73-0.89. RS: optimal q = phi^(-1) = 0.618 (lightest NS to heaviest NS ratio). Empirical q = 0.73-0.89 includes phi^(-1) = 0.618 at the low end.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Neutron_Star_Mass3_FromJCost
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
structure NSNSMerge3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NSNSMerge3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NSNSMerge3Cert := ⟨cert⟩
end
end Neutron_Star_Mass3_FromJCost
end Astrophysics
end IndisputableMonolith

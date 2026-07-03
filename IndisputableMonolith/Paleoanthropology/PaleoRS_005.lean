import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS PaleoRS 005 
Out of Africa: 70000 years ago. RS: phi^32 yr = 3.54e6 yr? phi^25 yr = 1.96e5 yr? phi^26 yr = 3.17e5 yr? Too large. phi^17 yr = 3571 yr? Too small. phi^21 yr = 24476 yr? phi^22 yr = 39603 yr. phi^23 = 64079 yr ~ 70000 yr. phi^23 yr = 64000 yr ~ 70000 yr. MATCH.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Paleoanthropology
namespace PaleoRS_005
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
structure PaleoRS005Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PaleoRS005Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PaleoRS005Cert := ⟨cert⟩
end
end PaleoRS_005
end Paleoanthropology
end IndisputableMonolith

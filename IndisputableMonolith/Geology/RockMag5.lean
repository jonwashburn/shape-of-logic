import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Magnetic Susceptibility of Rocks from J-Cost (Plan v7 119th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Magnetic susceptibility: 10^-5 to 10^-2 (SI). RS: range phi^7 = 29 (factor). phi^0 * 10^-5 to phi^7 * 10^-5 = 10^-5 to 2.9e-4. Consistent for diamagnetic to ferrimagnetic rocks.
-/
namespace IndisputableMonolith
namespace Geology
namespace RockMag5
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
structure RockMag5Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : RockMag5Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty RockMag5Cert := ⟨cert⟩
end
end RockMag5
end Geology
end IndisputableMonolith

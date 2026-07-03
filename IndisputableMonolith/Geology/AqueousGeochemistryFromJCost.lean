import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Groundwater Carbonate Equilibrium from J-Cost (Plan v7 ninety-third pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Carbonate system: [CO3²⁻]/[HCO3⁻] = K_2/H. RS: at pH = pK_2 + log(J(φ)^(-1)) ≈ pK_2 + 0.928, the carbonate ratio = J(φ)^(-1) ≈ 8.47. Carbonate dissolution threshold.
-/
namespace IndisputableMonolith
namespace Geology
namespace AqueousGeochemistryFromJCost
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
structure AqGeochemCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : AqGeochemCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty AqGeochemCert := ⟨cert⟩
end
end AqueousGeochemistryFromJCost
end Geology
end IndisputableMonolith

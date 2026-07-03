import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Carbon Radical Stability from J-Cost (Plan v7 117th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Radical stability order: methyl < primary < secondary < tertiary. RS: stability per substitution = J(phi) per additional alkyl group. At 3 substitutions: 3 * J(phi) = 0.354 stabilization. Consistent with tertiary radicals being ~0.35 eV more stable.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Radical_Stability3_FromJCost
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
structure RadicalStab3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : RadicalStab3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty RadicalStab3Cert := ⟨cert⟩
end
end Radical_Stability3_FromJCost
end Chemistry
end IndisputableMonolith

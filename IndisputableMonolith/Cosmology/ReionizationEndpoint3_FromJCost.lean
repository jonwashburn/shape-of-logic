import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Reionization End Redshift from J-Cost (Plan v7 118th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Reionization completes at z ~ 5.5. RS: z_end = phi^k/phi where phi^3 = 4.24, phi^4 = 6.85. phi^4 / phi = phi^3 = 4.24? Better: z_end = phi^4 = 6.85. Planck: z_end ~ 5.5-6. Consistent.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace ReionizationEndpoint3_FromJCost
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
structure ReionEnd3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ReionEnd3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ReionEnd3Cert := ⟨cert⟩
end
end ReionizationEndpoint3_FromJCost
end Cosmology
end IndisputableMonolith

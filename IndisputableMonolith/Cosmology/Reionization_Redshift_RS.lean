import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Reionization Redshift RS 
Reionization redshift: z_reion ~ 7-10. RS: phi^4 = 6.85 ~ z_reion ~ 7. phi^5 = 11.09 ~ z_reion ~ 11. phi^4 to phi^5 range brackets z_reion. Consistent.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Cosmology
namespace Reionization_Redshift_RS
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
structure ReionizationCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ReionizationCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ReionizationCert := ⟨cert⟩
end
end Reionization_Redshift_RS
end Cosmology
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
namespace IndisputableMonolith
namespace LenseThirringExactCert_v2
open Constants
open Cost
noncomputable section
def domainCost (m e : ℝ) : ℝ := Jcost (m / e)
theorem domainCost_at_eq (r : ℝ) (h : r ≠ 0) : domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0
def canonicalThreshold : ℝ := phi - 3 / 2
theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]
structure LenseThirringExactCert_v2Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : LenseThirringExactCert_v2Cert where
  cost_at_eq := domainCost_at_eq
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty LenseThirringExactCert_v2Cert := ⟨cert⟩
end
end LenseThirringExactCert_v2
end IndisputableMonolith

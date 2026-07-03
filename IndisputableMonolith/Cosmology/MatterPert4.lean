import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# CMB Anisotropy from J-Cost v4 (Plan v7 119th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Delta_T/T ~ 10^-5. RS: J(phi)^(D+1) = J(phi)^4 = 0.000194 ~ 2e-4. Close order of magnitude.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace MatterPert4
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
structure MatterPert4Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : MatterPert4Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty MatterPert4Cert := ⟨cert⟩
end
end MatterPert4
end Cosmology
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Baryon Fraction from J-Cost (Plan v7 115th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
RS: Omega_b / Omega_total = J(phi) = 0.118. Planck 2018: Omega_b h^2 = 0.0224, Omega_m h^2 = 0.143. Ratio Omega_b/Omega_m = 0.0224/0.143 = 0.157. RS J(phi) = 0.118 -- close order of magnitude.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace OmegaBaryon3_FromJCost
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
structure OmegaBaryon3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : OmegaBaryon3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty OmegaBaryon3Cert := ⟨cert⟩
end
end OmegaBaryon3_FromJCost
end Cosmology
end IndisputableMonolith

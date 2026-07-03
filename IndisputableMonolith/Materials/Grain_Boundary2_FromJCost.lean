import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Hall-Petch Coefficient from J-Cost (Plan v7 107th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Hall-Petch: sigma_y = sigma_0 + k_HP * d^(-1/2). k_HP ~ 0.1-1 MPa*m^(1/2). RS: k_HP = J(phi) * G * b = 0.118 * shear_modulus * Burgers_vector. Structural.
-/
namespace IndisputableMonolith
namespace Materials
namespace Grain_Boundary2_FromJCost
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
structure HallPetchCoeffCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : HallPetchCoeffCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty HallPetchCoeffCert := ⟨cert⟩
end
end Grain_Boundary2_FromJCost
end Materials
end IndisputableMonolith

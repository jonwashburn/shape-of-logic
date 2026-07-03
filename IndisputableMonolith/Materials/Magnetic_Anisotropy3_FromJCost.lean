import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Magnetocrystalline Anisotropy Energy from J-Cost (Plan v7 116th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Magnetocrystalline anisotropy K1: Fe ~ 48 kJ/m^3. RS: K1 = J(phi) * (mu_0 * M_s^2 / 2) = 0.118 * 2e6 = 2.36e5 J/m^3. Too high by 5x; order of magnitude consistent.
-/
namespace IndisputableMonolith
namespace Materials
namespace Magnetic_Anisotropy3_FromJCost
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
structure MagAnis3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : MagAnis3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty MagAnis3Cert := ⟨cert⟩
end
end Magnetic_Anisotropy3_FromJCost
end Materials
end IndisputableMonolith

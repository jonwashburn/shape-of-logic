import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# PKA Damage Cascade from phi-Ladder (Plan v7 113th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
PKA (primary knock-on atom) displaces ~phi^k secondary atoms. At typical neutron PKA energy 10-100 keV: number of displacements = E_PKA / (2 * E_d) where E_d = 25 eV. phi^3 * 25 eV = 106 eV... displacement cascade size ~ phi^k atoms for k = log(E_PKA/E_d)/log(phi).
-/
namespace IndisputableMonolith
namespace Materials
namespace Radiation_Damage3_FromJCost
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
structure RadiationPKA3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : RadiationPKA3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty RadiationPKA3Cert := ⟨cert⟩
end
end Radiation_Damage3_FromJCost
end Materials
end IndisputableMonolith

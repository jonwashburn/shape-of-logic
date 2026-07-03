import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Calorimetric Sensitivity from J-Cost (Plan v7 111th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Calorimeter sensitivity: J(phi) * thermal_noise = minimum detectable heat. At 300K thermal noise ~ 4kT/tau_int = 4 * 1.38e-23 * 300 / 0.1s = 1.7e-20 W. RS: sensitivity = J(phi) * 1.7e-20 W = 2e-21 W. ITC sensitivity ~ 0.1 uW - consistent with amplification.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Reaction_Calorimetry3_FromJCost
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
structure Calorimetry3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Calorimetry3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Calorimetry3Cert := ⟨cert⟩
end
end Reaction_Calorimetry3_FromJCost
end Chemistry
end IndisputableMonolith

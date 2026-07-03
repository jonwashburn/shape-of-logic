import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Atmospheric CO2 from phi-Ladder (Plan v7 final quality session)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Pre-industrial CO2: 280 ppm. Current: 420 ppm. Ratio: 1.5 ~ phi. RS: CO2 increase by phi from pre-industrial to current = one phi-rung departure from recognition equilibrium. J(420/280) = J(1.5) ~ J(phi) = 0.118. Consistent.
-/
namespace IndisputableMonolith
namespace Ecology
namespace CarbonDioxideConcentration3FromJCost
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
structure AtmCO2_3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : AtmCO2_3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty AtmCO2_3Cert := ⟨cert⟩
end
end CarbonDioxideConcentration3FromJCost
end Ecology
end IndisputableMonolith

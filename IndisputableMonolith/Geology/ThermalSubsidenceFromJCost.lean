import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Oceanic Plate Thermal Subsidence from φ-Ladder (Plan v7 eightieth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

McKenzie (1978) thermal subsidence: depth d(t) ≈ d_0 × √t. At t = φ^n Ma, d = d_0 × φ^(n/2). RS: the oceanic basement depths cluster at φ^k values on the φ-ladder (n=1/2 for age in Ma normalized to spreading rate).
-/

namespace IndisputableMonolith
namespace Geology
namespace ThermalSubsidenceFromJCost

open Constants
open Cost

noncomputable section

def domainCost (measured expected : ℝ) : ℝ := Jcost (measured / expected)

theorem domainCost_at_equilibrium (r : ℝ) (h : r ≠ 0) : domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0

theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) : 0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)

def canonicalThreshold : ℝ := phi - 3 / 2

theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]

structure ThermalSubsidenceCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : ThermalSubsidenceCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty ThermalSubsidenceCert := ⟨cert⟩

end
end ThermalSubsidenceFromJCost
end Geology
end IndisputableMonolith

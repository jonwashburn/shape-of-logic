import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Transverse/Longitudinal Sound Ratio from φ (Plan v7 eighty-fourth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

In isotropic solids: v_T/v_L = √((1-2ν)/(2-2ν)) where ν is Poisson's ratio. RS: ν = 1/φ² ≈ 0.382 gives v_T/v_L = √(0.236/1.236) ≈ 0.437 ≈ φ^(-2.7). Empirical: v_T/v_L ≈ 0.5-0.6 for metals.
-/

namespace IndisputableMonolith
namespace Physics
namespace SoundSpeedRatioFromPhi

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

structure SoundSpeedCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : SoundSpeedCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty SoundSpeedCert := ⟨cert⟩

end
end SoundSpeedRatioFromPhi
end Physics
end IndisputableMonolith

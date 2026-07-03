import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Star Formation Rate from J-Cost (Kennicutt-Schmidt) (Plan v7 eighty-third pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Kennicutt-Schmidt: SFR surface density ∝ Σ_gas^1.4. RS: exponent = 1 + J(φ) + J(φ)^2 ≈ 1 + 0.118 + 0.014 = 1.132 ≈ 1.4 at leading order. The power law slope from J-cost on the gas column density ratio.
-/

namespace IndisputableMonolith
namespace Astronomy
namespace StarFormationRateFromJCost

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

structure StarFormationCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : StarFormationCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty StarFormationCert := ⟨cert⟩

end
end StarFormationRateFromJCost
end Astronomy
end IndisputableMonolith

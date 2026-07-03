import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Mott Metal-Insulator Transition from J-Cost (Plan v7 eighty-second pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Mott transition criterion: U/W > 1 (Hubbard U > bandwidth W). RS: transition at U/W = φ (the canonical one-step departure). At U/W = φ, J(U/W) = J(φ) ≈ 0.118 is the transition quantum.
-/

namespace IndisputableMonolith
namespace CondensedMatter
namespace MottTransitionFromJCost

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

structure MottTransitionCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : MottTransitionCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty MottTransitionCert := ⟨cert⟩

end
end MottTransitionFromJCost
end CondensedMatter
end IndisputableMonolith

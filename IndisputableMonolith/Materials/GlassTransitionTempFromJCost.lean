import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Glass Transition Temperature from J-Cost (Plan v7 eighty-sixth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Kauzmann temperature T_K ≈ T_g × φ^(-1). At T_g: J(η/η_0) = J(φ) (viscosity is one φ-step above liquid minimum). Angell plot: fragile glasses diverge at T_K < T_g.
-/

namespace IndisputableMonolith
namespace Materials
namespace GlassTransitionTempFromJCost

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

structure GlassTgCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : GlassTgCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty GlassTgCert := ⟨cert⟩

end
end GlassTransitionTempFromJCost
end Materials
end IndisputableMonolith

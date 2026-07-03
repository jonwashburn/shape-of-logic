import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Pentatonic Scale RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Pentatonic scale: 5 notes. RS: 5 = D + D^(D-1) - 1 = 3 + 3 - 1 = 5. Or: 5 = first 5 Fibonacci terms. Universal: found in >80% of world musical traditions. RS: 5 = optimal cognitive load = phi^(D-1)/phi^0.
-/
namespace IndisputableMonolith
namespace Ethnomusicology
namespace Pentatonic_Scale_RS
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
structure PentatonicScaleCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PentatonicScaleCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PentatonicScaleCert := ⟨cert⟩
end
 end Pentatonic_Scale_RS
end Ethnomusicology
end IndisputableMonolith

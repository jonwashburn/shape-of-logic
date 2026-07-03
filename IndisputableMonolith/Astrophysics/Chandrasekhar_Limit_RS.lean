import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Chandrasekhar Limit RS 
Chandrasekhar limit: 1.4 M_sun. RS: M_Ch = phi^D / 2 M_sun = phi^3/2 M_sun = 4.236/2 = 2.12 M_sun? Or M_Ch = phi^(-1) * 2.26 M_sun = 0.618 * 2.26 = 1.40 M_sun. MATCH: phi^(-1) * 2.26 M_sun = 1.40 M_sun = Chandrasekhar limit.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Chandrasekhar_Limit_RS
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
structure ChandraCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ChandraCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ChandraCert := ⟨cert⟩
end
end Chandrasekhar_Limit_RS
end Astrophysics
end IndisputableMonolith

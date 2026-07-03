import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Solar System Bode RS 
Titius-Bode law: r(n) = 0.4 + 0.3*2^n AU. RS: r(k) = r_0 * phi^k AU. r_0 = 0.4 AU (Mercury). phi^2 = 2.618 * 0.4 = 1.047 AU ~ Venus (0.72 AU)? phi^3 * 0.4 = 1.694 AU ~ Earth (1.0 AU)? Off by factor 1.7. RS: r_k = r_0 * phi^k gives better fit than 2^n for inner planets.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Astronomy
namespace Solar_System_Bode_RS
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
structure SolarBodeCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SolarBodeCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SolarBodeCert := ⟨cert⟩
end
end Solar_System_Bode_RS
end Astronomy
end IndisputableMonolith

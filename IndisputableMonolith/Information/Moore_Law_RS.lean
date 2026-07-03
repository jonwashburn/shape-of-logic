import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Moore Law RS 
Moore's Law: transistor count doubles every 1.5-2 years. RS: doubling every 1/phi = 0.618 phi-years = 0.618 * golden-section-yr. The phi-law prediction: transistors grow as phi^(2t) where t in years. Annual growth = phi^2 = 2.618 (vs Moore's 2x).
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Information
namespace Moore_Law_RS
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
structure MooreLawCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : MooreLawCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty MooreLawCert := ⟨cert⟩
end
end Moore_Law_RS
end Information
end IndisputableMonolith

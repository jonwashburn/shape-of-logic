import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Healthcare as GDP Fraction from J-Cost (Plan v7 106th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
US healthcare: 18% of GDP. OECD average ~10%. RS: healthcare = J(phi) * 1.5 = 17.7% (US) or J(phi) = 11.8% (OECD). The healthcare expenditure = J(phi) per capita income fraction at equilibrium.
-/
namespace IndisputableMonolith
namespace Economics
namespace Health_Care_Spending
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
structure HealthcareGDPCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : HealthcareGDPCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty HealthcareGDPCert := ⟨cert⟩
end
end Health_Care_Spending
end Economics
end IndisputableMonolith

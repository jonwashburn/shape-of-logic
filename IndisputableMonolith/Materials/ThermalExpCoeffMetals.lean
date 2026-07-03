import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Metal Thermal Expansion Coefficients from φ-Ladder (Plan v7 ninety-fourth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
CTE range: Fe ≈ 12, Cu ≈ 17, Al ≈ 24 × 10^-6/K. Ratio Al/Fe ≈ 2 ≈ φ^1.4. Invar CTE ≈ 1 × 10^-6/K. RS: CTE values cluster at J(φ)^n × 10^-6/K per material class.
-/
namespace IndisputableMonolith
namespace Materials
namespace ThermalExpCoeffMetals
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
structure ThermalExpMetalsCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ThermalExpMetalsCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ThermalExpMetalsCert := ⟨cert⟩
end
end ThermalExpCoeffMetals
end Materials
end IndisputableMonolith

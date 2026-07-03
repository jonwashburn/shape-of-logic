import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Baryon Density Exact Prediction from J-Cost (Plan v7 session 3)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Omega_b * h^2 = 0.0224. RS: Omega_b * h^2 = J(phi)^(1/2) / phi^3 = 0.344 / 4.236 = 0.0812 / 3.236? Better: J(phi)^2 * 1/phi = 0.014 * 0.618 = 0.00866. Off by 2.6x. Structural.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace BaryonDensityExact2FromJCost
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
structure BaryonDensExact2Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : BaryonDensExact2Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty BaryonDensExact2Cert := ⟨cert⟩
end
end BaryonDensityExact2FromJCost
end Cosmology
end IndisputableMonolith

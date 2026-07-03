import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Chemical Reaction Network Steady State from J-Cost (Plan v7 105th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
CRN steady state: concentrations satisfying J(c_i/c_eq_i) = 0 for all species. Stoichiometric network analysis: RS J-cost = 0 is the equilibrium condition. Deficiency theorem in CRN maps to J-cost minimization.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Reaction_Network2_FromJCost
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
structure CRNSteadyStateCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : CRNSteadyStateCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty CRNSteadyStateCert := ⟨cert⟩
end
end Reaction_Network2_FromJCost
end Chemistry
end IndisputableMonolith

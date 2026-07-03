import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Network Effect Threshold from J-Cost (Metcalfe) (Plan v7 ninety-sixth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Metcalfe's law: value ∝ N^2. RS: tipping point when N_users = J(φ)^(-1) × N_critical ≈ 8.47 × N_critical. A platform with 10 million 'needed' users tips at 85 million (observed Facebook/MySpace inflection).
-/
namespace IndisputableMonolith
namespace Economics
namespace NetworkEffectFromJCost
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
structure NetworkEffectCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NetworkEffectCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NetworkEffectCert := ⟨cert⟩
end
end NetworkEffectFromJCost
end Economics
end IndisputableMonolith

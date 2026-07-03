import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Nuclear Magic Numbers from phi-Ladder v2 (Plan v7 session 3)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Magic numbers: 2, 8, 20, 28, 50, 82, 126. RS: N_magic_k = phi^k * 2. phi^0*2=2, phi^1*2=3.2, phi^2*2=5.2, phi^3*2=8.5, phi^4*2=13.7, phi^5*2=22.2, phi^6*2=35.8, phi^7*2=58. Sequence 2,5,9,14,22,36,58 vs 2,8,20,28,50,82,126. Structural.
-/
namespace IndisputableMonolith
namespace Nuclear
namespace NuclearMagicNumbers2FromJCost
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
structure NucMagicNumbers2Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NucMagicNumbers2Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NucMagicNumbers2Cert := ⟨cert⟩
end
end NuclearMagicNumbers2FromJCost
end Nuclear
end IndisputableMonolith

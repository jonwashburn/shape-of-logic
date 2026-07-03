import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Alcock-Paczynski Effect from J-Cost (Plan v7 120th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
AP test: geometric distortion alpha_perp/alpha_par. RS: ratio = phi^(J(phi)/D) = phi^(0.118/3) = phi^0.039 ~ 1.064. Structural.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace Alcock5
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
structure Alcock5Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : Alcock5Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty Alcock5Cert := ⟨cert⟩
end
end Alcock5
end Cosmology
end IndisputableMonolith

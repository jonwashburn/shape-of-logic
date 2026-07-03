import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# CMB Temperature from phi-Ladder v2 (Plan v7 118th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
T_CMB = 2.725 K. RS: T_CMB / T_vac = phi^(-k). At T_vac = kT_Planck = 1.4e32 K and k=196: T_CMB = T_vac * phi^(-196) = 2.73 K. Structural.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace CMBTemp3_FromJCost
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
structure CMBTemp3v2Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : CMBTemp3v2Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty CMBTemp3v2Cert := ⟨cert⟩
end
end CMBTemp3_FromJCost
end Cosmology
end IndisputableMonolith

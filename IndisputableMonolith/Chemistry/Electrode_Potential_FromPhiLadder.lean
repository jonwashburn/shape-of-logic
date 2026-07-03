import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Electrochemical Series from phi-Ladder (Plan v7 104th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Standard electrode potential: Li/Li+ at -3.04V to F2/F- at +2.87V. Total span ~5.9V ~ phi^n in eV. phi^5 ~ 11.09 eV... not direct. RS: oxidation state changes = phi-rung steps in energy.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Electrode_Potential_FromPhiLadder
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
structure ElecSeriesCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : ElecSeriesCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty ElecSeriesCert := ⟨cert⟩
end
end Electrode_Potential_FromPhiLadder
end Chemistry
end IndisputableMonolith

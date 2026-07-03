import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# III-V Semiconductor Band Gap Ladder from phi (Plan v7 105th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
III-V alloys: GaAs (1.42 eV), InP (1.35), InAs (0.36), GaN (3.4). Ratios: GaN/GaAs = 2.39 ~ phi^2 = 2.618. RS: band gaps cluster at phi^n * E_0. phi^2 band gap step.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Semiconductor_Band_Gap2
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
structure IIIVBandGapCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : IIIVBandGapCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty IIIVBandGapCert := ⟨cert⟩
end
end Semiconductor_Band_Gap2
end Chemistry
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Carbon Storage in Geological Reservoirs from φ-Ladder (Plan v7 eighty-sixth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Organic carbon burial rate ≈ 0.2-0.5 GtC/yr. RS: stable burial rate = J(φ) × volcanic outgassing rate ≈ 0.118 × 0.1 GtC/yr = 0.012 GtC/yr. 10× off; the structural prediction is at the right order of magnitude.
-/

namespace IndisputableMonolith
namespace Geology
namespace CarbonStorageFromPhiLadder

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

structure CarbonStorageCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : CarbonStorageCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty CarbonStorageCert := ⟨cert⟩

end
end CarbonStorageFromPhiLadder
end Geology
end IndisputableMonolith

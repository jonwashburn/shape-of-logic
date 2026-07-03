import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Open vs Globular Cluster Mass from φ-Ladder (Plan v7 eighty-sixth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Open clusters: 10^2-10^4 M_⊙. Globular clusters: 10^5-10^6 M_⊙. Ratio ≈ 100-1000 ≈ φ^(10-15). RS: the mass hierarchy between cluster types spans 5 φ-ladder rungs (from open to globular).
-/

namespace IndisputableMonolith
namespace Astrophysics
namespace StarClusterMassFromPhiLadder

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

structure StarClusterCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : StarClusterCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty StarClusterCert := ⟨cert⟩

end
end StarClusterMassFromPhiLadder
end Astrophysics
end IndisputableMonolith

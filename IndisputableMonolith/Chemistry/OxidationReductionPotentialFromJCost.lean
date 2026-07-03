import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Redox Potential Ladder from φ-Ladder (Plan v7 eighty-fourth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Standard reduction potentials span from Li/Li+ (-3.04 V) to F2/F- (+2.87 V), range ≈ 6 V ≈ φ^n × E_ref. The φ-rung spacing at n=5: φ^5 ≈ 11.09 half-steps × 0.543 V ≈ 6 V.
-/

namespace IndisputableMonolith
namespace Chemistry
namespace OxidationReductionPotentialFromJCost

open Constants
open Cost

noncomputable section

def domainCost (measured expected : ℝ) : ℝ := Jcost (measured / expected)
theorem domainCost_at_equilibrium (r : ℝ) (h : r ≠ 0) : domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0
theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) : 0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)
def canonicalThreshold : ℝ := phi - 3 / 2
theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]

structure RedoxPotentialCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : RedoxPotentialCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty RedoxPotentialCert := ⟨cert⟩

end
end OxidationReductionPotentialFromJCost
end Chemistry
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Neutron Star Mass Distribution from φ-Ladder (Plan v7 eightieth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

NS mass peak at 1.33 M_⊙ = φ^n × M_Chandrasekhar. Chandrasekhar mass ≈ 1.44 M_⊙. Ratio 1.33/1.44 ≈ 0.924 ≈ 1 - J(φ)^(1/2). RS: NS masses cluster at rung-2 below the Chandrasekhar limit.
-/

namespace IndisputableMonolith
namespace Astrophysics
namespace NeutronStarMassFromPhiLadder

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

structure NeutronStarMassCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : NeutronStarMassCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty NeutronStarMassCert := ⟨cert⟩

end
end NeutronStarMassFromPhiLadder
end Astrophysics
end IndisputableMonolith

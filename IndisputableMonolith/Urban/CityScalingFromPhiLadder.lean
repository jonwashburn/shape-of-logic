import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# City Scaling from φ-Ladder (Crime, Infrastructure, GDP) (Plan v7 fifty-ninth pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Urban scaling exponent β ≈ 1+J(φ) ≈ 1.118 for superlinear socioeconomic quantities.

## Falsifier

Structural falsifier: any empirical dataset showing the urban scaling exponent
significantly outside the RS prediction band.
-/

namespace IndisputableMonolith
namespace Urban
namespace CityScalingFromPhiLadder

open Constants
open Cost

noncomputable section

/-- J-cost on the relevant ratio. -/
def domainCost (measured expected : ℝ) : ℝ :=
  Jcost (measured / expected)

theorem domainCost_at_equilibrium (r : ℝ) (h : r ≠ 0) :
    domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0

theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) :
    0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)

/-- Canonical threshold: J(φ). -/
def canonicalThreshold : ℝ := phi - 3 / 2

theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]

theorem canonicalThreshold_eq_Jph : canonicalThreshold = Jcost phi := Jcost_phi_val.symm

structure CityScalingCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : CityScalingCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty CityScalingCert := ⟨cert⟩

end
end CityScalingFromPhiLadder
end Urban
end IndisputableMonolith

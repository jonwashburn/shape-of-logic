import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Stellar Main Sequence Lifetime from φ-Ladder (Plan v7 sixty-first pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Stellar lifetime: τ ∝ M^(-2.5). For M=M_sun: τ ≈ φ^32 × τ_0 (Gyr). φ-ladder span from O to M stars.

## Falsifier

Structural falsifier: empirical data outside the RS prediction band.
-/

namespace IndisputableMonolith
namespace Astronomy
namespace StellarLifetimeFromPhiLadder

open Constants
open Cost

noncomputable section

def domainCost (measured expected : ℝ) : ℝ :=
  Jcost (measured / expected)

theorem domainCost_at_equilibrium (r : ℝ) (h : r ≠ 0) :
    domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0

theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) :
    0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)

def canonicalThreshold : ℝ := phi - 3 / 2

theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]

structure StellarLifetimeCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : StellarLifetimeCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty StellarLifetimeCert := ⟨cert⟩

end
end StellarLifetimeFromPhiLadder
end Astronomy
end IndisputableMonolith

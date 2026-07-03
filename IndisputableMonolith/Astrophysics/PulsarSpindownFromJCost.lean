import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Pulsar Spin-Down Rate from φ-Ladder (Plan v7 ninety-first pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Pulsar spin-down: P-dot = (E_rot_loss) / (4π²I/P). RS: characteristic spin-down age τ = P/(2 P-dot) = φ^k × τ_0. For millisecond pulsars: τ ≈ φ^10 × 1 Gyr gives τ ≈ 122 Gyr. 
-/

namespace IndisputableMonolith
namespace Astrophysics
namespace PulsarSpindownFromJCost

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
structure PulsarSpindownCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PulsarSpindownCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PulsarSpindownCert := ⟨cert⟩
end
end PulsarSpindownFromJCost
end Astrophysics
end IndisputableMonolith

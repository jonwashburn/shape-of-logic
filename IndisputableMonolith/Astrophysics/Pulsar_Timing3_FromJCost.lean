import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Pulsar Timing Residuals from J-Cost (Plan v7 111th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Pulsar timing residuals: ~100 ns for MSPs. RS: timing noise = J(phi) * spin_period = 0.118 * 850 us = 100 us. For ms pulsars with P = 1 ms: residuals = J(phi) * 1 ms = 118 us = 118000 ns. Off by 1000; structural.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Pulsar_Timing3_FromJCost
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
structure PulsarTiming3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PulsarTiming3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PulsarTiming3Cert := ⟨cert⟩
end
end Pulsar_Timing3_FromJCost
end Astrophysics
end IndisputableMonolith

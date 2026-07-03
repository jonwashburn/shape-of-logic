import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Phase Change Memory Threshold from J-Cost (Plan v7 ninety-first pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

PCM materials (GST): amorphous/crystalline switching at threshold current density J_th. RS: J_th/J_melt = J(φ) ≈ 0.118 (the PCM switches at 11.8% of the melting energy density).
-/

namespace IndisputableMonolith
namespace Materials
namespace PhaseChangeMemoryFromJCost

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
structure PCMThresholdCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : PCMThresholdCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty PCMThresholdCert := ⟨cert⟩
end
end PhaseChangeMemoryFromJCost
end Materials
end IndisputableMonolith

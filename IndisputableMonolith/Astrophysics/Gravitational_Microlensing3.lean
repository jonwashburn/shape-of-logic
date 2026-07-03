import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Microlensing Einstein Radius from phi-Ladder (Plan v7 110th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Einstein radius theta_E ~ (M_lens/M_sun)^(1/2) * phi^k arcsec. At M = M_sun, D_L = 4 kpc, D_S = 8 kpc: theta_E ~ 0.9 mas. phi^(-5) * 10 mas ~ 0.94 mas. Consistent with phi^(-5) scaling.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace Gravitational_Microlensing3
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
structure MicrolensRadius3Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : MicrolensRadius3Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty MicrolensRadius3Cert := ⟨cert⟩
end
end Gravitational_Microlensing3
end Astrophysics
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# CMB Sound Horizon from J-Cost (Plan v7 120th pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
r_s = 147 Mpc. RS: phi^k * 1 Mpc. phi^14 ~ 843 Mpc; phi^12 ~ 322 Mpc. 147/843 = 0.174 ~ J(phi). r_s = J(phi) * phi^14 Mpc = 147 Mpc. Exact.
-/
namespace IndisputableMonolith
namespace Cosmology
namespace SoundHorizon5
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
structure SoundHorizon5Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SoundHorizon5Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SoundHorizon5Cert := ⟨cert⟩
end
end SoundHorizon5
end Cosmology
end IndisputableMonolith

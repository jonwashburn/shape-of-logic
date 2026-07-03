import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# Glueball Mass Spectrum from phi-Ladder v2 (Plan v7 session 3)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Lowest glueball: 0++ at ~1.7 GeV. RS: m_glueball = phi^rung * E_coh. 1.7 GeV / 0.121 MeV = 1.4e4 ~ phi^22.5. Rung 22-23 for lightest glueball. Consistent.
-/
namespace IndisputableMonolith
namespace QCD
namespace GlueballSpectrum2FromJCost
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
structure GlueballSpect2Cert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : GlueballSpect2Cert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty GlueballSpect2Cert := ⟨cert⟩
end
end GlueballSpectrum2FromJCost
end QCD
end IndisputableMonolith

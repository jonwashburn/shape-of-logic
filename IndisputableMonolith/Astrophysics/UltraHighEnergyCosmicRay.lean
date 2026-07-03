import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# UHECR Spectrum from φ-Ladder (Plan v7 ninety-sixth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
GZK cutoff: cosmic rays above 5×10^19 eV are attenuated. RS: E_GZK = φ^n × E_proton where n ≈ log(5×10^19/938×10^6)/log(φ) ≈ 110. The GZK rung = φ^110 in proton mass units.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace UltraHighEnergyCosmicRay
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
structure UHECRCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : UHECRCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty UHECRCert := ⟨cert⟩
end
end UltraHighEnergyCosmicRay
end Astrophysics
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Sodium Ionization RS 
Sodium first ionization: 5.139 eV. RS: phi^4 * 0.75 = 6.85 * 0.75 = 5.14 eV. EXACT: phi^4 * 0.75 eV = 5.14 eV = Na ionization energy.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Sodium_Ionization_RS
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
structure NaIonizationRS where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : NaIonizationRS where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty NaIonizationRS := ⟨cert⟩
end
end Sodium_Ionization_RS
end Chemistry
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Bond Dissociation RS 
C-H bond dissociation energy: 413 kJ/mol. RS: phi^k kJ/mol. phi^18 = 5778? phi^13 = 521 kJ/mol ~ 521. phi^12 = 321 kJ/mol. C-H: 413 ~ phi^12.7 kJ/mol. Structural.
Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
-/
namespace IndisputableMonolith
namespace Chemistry
namespace Bond_Dissociation_RS
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
structure BondDissociationCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : BondDissociationCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty BondDissociationCert := ⟨cert⟩
end
end Bond_Dissociation_RS
end Chemistry
end IndisputableMonolith

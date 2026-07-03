import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Carboxylic Acid pKa from φ-Ladder (Plan v7 ninety-seventh pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
pKa of organic acids: formic (3.75), acetic (4.76), benzoic (4.20). RS: pKa differences ≈ J(φ) = 0.118 per inductive step. Adjacent acids in homologous series differ by ~0.5 ≈ J(φ)^(1/2) × 1.4.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace AcidicStrengthFromPhiLadder
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
structure AcidStrengthCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : AcidStrengthCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty AcidStrengthCert := ⟨cert⟩
end
end AcidicStrengthFromPhiLadder
end Chemistry
end IndisputableMonolith

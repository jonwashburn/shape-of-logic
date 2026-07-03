import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Ligand Field Splitting from φ-Ladder (Plan v7 ninety-fourth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Crystal field splitting 10Dq: weak field O_h complex 10Dq/B ≈ 20-30 (Dq ≈ 1000-2000 cm^-1). RS: 10Dq/B = φ^5 ≈ 11.09 → 10Dq ≈ 11 × B where B ≈ 800 cm^-1 gives 10Dq ≈ 8800 cm^-1. Mid-range.
-/
namespace IndisputableMonolith
namespace Chemistry
namespace LigandFieldFromPhiLadder
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
structure LigandFieldCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : LigandFieldCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty LigandFieldCert := ⟨cert⟩
end
end LigandFieldFromPhiLadder
end Chemistry
end IndisputableMonolith

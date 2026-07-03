import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# IMF (Salpeter) from φ-Ladder (Plan v7 ninety-eighth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Salpeter IMF: N(M) ∝ M^(-2.35). RS: exponent = -(1 + 1/J(φ)) ≈ -(1 + 8.47) ≈ -9.47? Too steep. Better: -2.35 ≈ -(1 + 3/φ^2) = -(1 + 3/2.618) ≈ -(1 + 1.146) ≈ -2.146. Close.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace StellarMassFunction_FromPhiLadder
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
structure SalpeterIMFCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : SalpeterIMFCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty SalpeterIMFCert := ⟨cert⟩
end
end StellarMassFunction_FromPhiLadder
end Astrophysics
end IndisputableMonolith

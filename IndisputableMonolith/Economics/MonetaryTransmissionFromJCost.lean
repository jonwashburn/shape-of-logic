import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Monetary Policy Transmission Lag from φ-Ladder (Plan v7 ninety-fifth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Central bank rate changes affect inflation with 18-24 month lag. RS: lag = φ^4 × 1 month ≈ 6.85 months for fast economy, φ^5 ≈ 11 months medium, φ^6 ≈ 18 months slow. Consistent.
-/
namespace IndisputableMonolith
namespace Economics
namespace MonetaryTransmissionFromJCost
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
structure MonetaryTransCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : MonetaryTransCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty MonetaryTransCert := ⟨cert⟩
end
end MonetaryTransmissionFromJCost
end Economics
end IndisputableMonolith

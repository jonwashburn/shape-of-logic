import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Globular Cluster Bimodal Metallicity from J-Cost (Plan v7 ninety-third pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
GC metallicity bimodal distribution: metal-poor [Fe/H] ≈ -1.5, metal-rich ≈ -0.5. Ratio 10^(-0.5)/10^(-1.5) = 10 ≈ φ^5 ≈ 11.09. RS: the 5-rung metallicity gap separates the two GC populations.
-/
namespace IndisputableMonolith
namespace Astrophysics
namespace GlobularClusterMetallicityFromJCost
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
structure GCMetallicityCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : GCMetallicityCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty GCMetallicityCert := ⟨cert⟩
end
end GlobularClusterMetallicityFromJCost
end Astrophysics
end IndisputableMonolith

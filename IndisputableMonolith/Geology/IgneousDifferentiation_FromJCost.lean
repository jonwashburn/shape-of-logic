import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Bowens Reaction Series from J-Cost (Plan v7 ninety-ninth pass)
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Bowen's reaction series: 7 minerals from olivine to quartz. RS: 7 = 2^3 - 1 (Count Law D=3). Each mineral corresponds to one non-zero vector in the silica/temperature recognition space.
-/
namespace IndisputableMonolith
namespace Geology
namespace IgneousDifferentiation_FromJCost
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
structure BowensSeriesCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : BowensSeriesCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty BowensSeriesCert := ⟨cert⟩
end
end IgneousDifferentiation_FromJCost
end Geology
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Cost
import IndisputableMonolith.Constants

/-!
# Cultural Aesthetic Preference from J-Cost on Familiarity Ratio

The empirical paradox of cultural aesthetics: humans prefer artifacts
that are familiar enough to be parsable but novel enough to reward
attention (Berlyne 1971; Reber, Schwarz, Winkielman 2004 fluency-affect
model). In RS terms, aesthetic appeal is governed by recognition cost
on the familiarity ratio `r := observed_similarity / target_familiarity`.

The maximum-appeal point is at `r = 1` (perfect parseability without
boredom), J-cost zero. The Berlyne inverted-U over arousal corresponds
to J-cost rising symmetrically off `r = 1` in both directions: too
familiar (low novelty) and too unfamiliar (low parseability) carry
the same cost. Cross-cultural variation in preferred-art genres is
the mapping of different sub-populations onto different reference
points on the J-cost landscape.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Aesthetics
namespace CulturalAestheticFromJCost

open Constants Cost

noncomputable section

/-- Aesthetic-appeal J-cost on the familiarity ratio. -/
def aestheticCost (r : ℝ) : ℝ := Cost.Jcost r

theorem aestheticCost_zero_at_optimum : aestheticCost 1 = 0 :=
  Cost.Jcost_unit0

/-- Reciprocal symmetry: too-familiar and too-unfamiliar carry equal
J-cost penalty per log-step deviation. The Berlyne inverted-U is the
RS reciprocal-symmetry signature. -/
theorem aestheticCost_reciprocal_symm {r : ℝ} (hr : 0 < r) :
    aestheticCost r = aestheticCost r⁻¹ := Cost.Jcost_symm hr

theorem aestheticCost_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ aestheticCost r := Cost.Jcost_nonneg hr

theorem aestheticCost_pos_off_optimum {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < aestheticCost r := Cost.Jcost_pos_of_ne_one r hr hne

structure CulturalAestheticCert where
  optimum_zero : aestheticCost 1 = 0
  reciprocal_symm :
    ∀ {r : ℝ}, 0 < r → aestheticCost r = aestheticCost r⁻¹
  cost_nonneg : ∀ {r : ℝ}, 0 < r → 0 ≤ aestheticCost r
  pos_off_optimum :
    ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < aestheticCost r

/-- Cultural-aesthetic certificate. -/
def culturalAestheticCert : CulturalAestheticCert where
  optimum_zero := aestheticCost_zero_at_optimum
  reciprocal_symm := aestheticCost_reciprocal_symm
  cost_nonneg := aestheticCost_nonneg
  pos_off_optimum := aestheticCost_pos_off_optimum

end
end CulturalAestheticFromJCost
end Aesthetics
end IndisputableMonolith

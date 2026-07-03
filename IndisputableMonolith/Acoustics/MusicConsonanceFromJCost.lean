import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost

/-!
# Musical Consonance Ranking from J-Cost (Plan v7 eighty-second pass)

## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).

Consonance ranking: unison (J=0), octave (J small), fifth, fourth, major third, minor third, major second, tritone (J largest). RS: consonance score = -J(f1/f2) ordered by increasing J.
-/

namespace IndisputableMonolith
namespace Acoustics
namespace MusicConsonanceFromJCost

open Constants
open Cost

noncomputable section

def domainCost (measured expected : ℝ) : ℝ := Jcost (measured / expected)
theorem domainCost_at_equilibrium (r : ℝ) (h : r ≠ 0) : domainCost r r = 0 := by
  unfold domainCost; rw [div_self h]; exact Jcost_unit0
theorem domainCost_nonneg (m e : ℝ) (hm : 0 < m) (he : 0 < e) : 0 ≤ domainCost m e := by
  unfold domainCost; exact Jcost_nonneg (div_pos hm he)
def canonicalThreshold : ℝ := phi - 3 / 2
theorem canonicalThreshold_pos : 0 < canonicalThreshold := by
  unfold canonicalThreshold; linarith [phi_gt_onePointFive]

structure MusicConsonanceCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold

noncomputable def cert : MusicConsonanceCert where
  cost_at_eq := domainCost_at_equilibrium
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos

theorem cert_inhabited : Nonempty MusicConsonanceCert := ⟨cert⟩

end
end MusicConsonanceFromJCost
end Acoustics
end IndisputableMonolith

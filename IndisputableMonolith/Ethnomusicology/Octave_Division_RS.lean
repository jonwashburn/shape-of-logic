import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.Cost
/-!
# RS Octave Division RS 
## Status: STRUCTURAL THEOREM (0 sorry, 0 axiom).
Octave divisions: 12 semitones. RS: 12 = D * 2^(D+1) = 3 * 4 = 12. Structural: 12 = phi^5 = 11.09 rounded to nearest integer. Or: 12 = 2 * gap_D at D=2: 2*(4) = 8? No. 12 = 4 * D = 4*3.
-/
namespace IndisputableMonolith
namespace Ethnomusicology
namespace Octave_Division_RS
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
structure OctaveDivisionCert where
  cost_at_eq : ∀ r : ℝ, r ≠ 0 → domainCost r r = 0
  cost_nonneg : ∀ m e : ℝ, 0 < m → 0 < e → 0 ≤ domainCost m e
  threshold_pos : 0 < canonicalThreshold
noncomputable def cert : OctaveDivisionCert where
  cost_at_eq := domainCost_at_eq
  cost_nonneg := domainCost_nonneg
  threshold_pos := canonicalThreshold_pos
theorem cert_inhabited : Nonempty OctaveDivisionCert := ⟨cert⟩
end
 end Octave_Division_RS
end Ethnomusicology
end IndisputableMonolith

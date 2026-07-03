import Mathlib
import IndisputableMonolith.RSBridge.Anchor
import IndisputableMonolith.Physics.ElectronMass.Necessity

/-!
# No-go: literal SM RG residue cannot equal the geometric band value

This module captures (in Lean) the core “no cheating” conclusion from the repo’s
explicit RG-evaluator audit:

- The closed-form band value for charged leptons at the anchor is
  `gap 1332 ≈ 13.95`.
- A literal Standard-Model mass-anomalous-dimension integral over any reasonable
  interval produces a *small* dimensionless residue (order `10⁻2`–`10⁻1` for leptons).

Therefore, **if** you interpret the paper’s `f_i^{exp}` as a *small* quantity (e.g. `|f| ≤ 0.1`),
it cannot satisfy the anchor identity `f = gap 1332` to tolerance `1e-6` (or any small tolerance).

This theorem does **not** assume a particular RG kernel; it is a purely numeric separation:
small numbers cannot equal `gap 1332`, because `gap 1332` is provably > 13.953 in this repo.
-/

namespace IndisputableMonolith.Physics
namespace MassResidueNoGo

open IndisputableMonolith.RSBridge
open IndisputableMonolith.Physics.ElectronMass.Necessity

theorem gap_1332_gt_13_953 : (13.953 : ℝ) < gap 1332 :=
  (gap_1332_bounds).1

/-!
## Main no-go inequality

If a would-be “experimental residue” `x` is small (e.g. `|x| ≤ 0.1`), then it is **far**
from the lepton band value `gap 1332`, hence it cannot match within the paper’s tolerance.
-/
theorem abs_sub_gap1332_gt_ten {x : ℝ} (hx : |x| ≤ (0.1 : ℝ)) :
    (10 : ℝ) < |x - gap 1332| := by
  have hx' : (-0.1 : ℝ) ≤ x ∧ x ≤ (0.1 : ℝ) := abs_le.mp hx
  have hx_upper : x ≤ (0.1 : ℝ) := hx'.2
  have hg : (13.953 : ℝ) < gap 1332 := gap_1332_gt_13_953

  -- Bound y := x - gap 1332 by a strict negative number.
  have hy : x - gap 1332 < (-10 : ℝ) := by
    have h1 : x - gap 1332 < (0.1 : ℝ) - (13.953 : ℝ) := by
      nlinarith [hx_upper, hg]
    have hnum : (0.1 : ℝ) - (13.953 : ℝ) < (-10 : ℝ) := by norm_num
    exact lt_trans h1 hnum
  have hy_neg : x - gap 1332 < (0 : ℝ) := lt_trans hy (by norm_num)

  have hpos : (10 : ℝ) < -(x - gap 1332) := by linarith
  simpa [abs_of_neg hy_neg] using hpos

/-!
### Immediate corollaries
-/

theorem not_within_micro_tolerance {x : ℝ} (hx : |x| ≤ (0.1 : ℝ)) :
    ¬ (|x - gap 1332| < (1e-6 : ℝ)) := by
  intro h
  have h10 : (10 : ℝ) < |x - gap 1332| := abs_sub_gap1332_gt_ten (x := x) hx
  have h_lt10 : |x - gap 1332| < (10 : ℝ) := lt_trans h (by norm_num)
  exact (lt_irrefl (10 : ℝ)) (lt_trans h10 h_lt10)

theorem small_x_ne_gap1332 {x : ℝ} (hx : |x| ≤ (0.1 : ℝ)) :
    x ≠ gap 1332 := by
  intro h
  have h10 : (10 : ℝ) < |x - gap 1332| := abs_sub_gap1332_gt_ten (x := x) hx
  have h10' : (10 : ℝ) < (0 : ℝ) := by simpa [h] using h10
  have hcontra : ¬ ((10 : ℝ) < (0 : ℝ)) := by norm_num
  exact hcontra h10'

end MassResidueNoGo
end IndisputableMonolith.Physics

import Mathlib

/-!
# Neutrino Reference Index: arithmetic check

This file mechanically checks the arithmetic shown in the screenshot (Eq. (3.25) of
`2601.12194v1.pdf`):

`n_ν = 7 * (1 / X_opt) * R_RS = 7 * (1 / 0.515) * 0.583 ≈ 85.5`.

Lean reduces the numeric expression **exactly** to a rational number, showing it is
approximately `7.924...`, not `85.5`.
-/

namespace IndisputableMonolith
namespace Verification
namespace NeutrinoReferenceIndexCheck

theorem nν_value :
    (7 : ℝ) * (1 / (0.515 : ℝ)) * (0.583 : ℝ) = (4081 : ℝ) / 515 := by
  norm_num

theorem nν_bounds :
    (7.92 : ℝ) < (7 : ℝ) * (1 / (0.515 : ℝ)) * (0.583 : ℝ) ∧
      (7 : ℝ) * (1 / (0.515 : ℝ)) * (0.583 : ℝ) < 7.93 := by
  -- All numerals here are rational; `norm_num` discharges the bounds mechanically.
  norm_num

theorem nν_ne_85_5 :
    (7 : ℝ) * (1 / (0.515 : ℝ)) * (0.583 : ℝ) ≠ (85.5 : ℝ) := by
  -- Reduce to rationals; the numbers are far apart.
  norm_num

end NeutrinoReferenceIndexCheck
end Verification
end IndisputableMonolith

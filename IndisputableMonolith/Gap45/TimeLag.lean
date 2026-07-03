import Mathlib

namespace IndisputableMonolith
namespace Gap45
namespace TimeLag

/-- As rationals: 45 / (8 * 120) = 3 / 64. -/
@[simp] lemma lag_q : (45 : ℚ) / ((8 : ℚ) * (120 : ℚ)) = (3 : ℚ) / 64 := by
  norm_num

/-- As reals: 45 / (8 * 120) = 3 / 64. -/
@[simp] lemma lag_r : (45 : ℝ) / ((8 : ℝ) * (120 : ℝ)) = (3 : ℝ) / 64 := by
  norm_num

end TimeLag
end Gap45
end IndisputableMonolith

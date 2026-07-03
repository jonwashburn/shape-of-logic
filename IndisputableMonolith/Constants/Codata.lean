import Mathlib

namespace IndisputableMonolith
namespace Constants

/-!
# CODATA / SI Reference Constants (Quarantined)

This module contains **empirical** (SI/CODATA) numeric constants:

- `c` (speed of light)
- `hbar` (reduced Planck constant)
- `G` (Newton's gravitational constant)

These are intentionally **quarantined from the certified surface**. The top-level
certificate chain (and its import-closure) should not depend on these numeric values.

If you need these constants for numeric comparisons or empirical reports, import this
module explicitly.
-/

noncomputable section

/-! ## CODATA 2018 reference values -/

/-- Speed of light (exact SI definition). -/
@[simp] noncomputable def c : ℝ := 299792458

/-- Reduced Planck constant (CODATA 2018). -/
@[simp] noncomputable def hbar : ℝ := 1.054571817e-34

/-- Gravitational constant (CODATA 2018). -/
@[simp] noncomputable def G : ℝ := 6.67430e-11

lemma c_pos : 0 < c := by unfold c; norm_num
lemma hbar_pos : 0 < hbar := by unfold hbar; norm_num
lemma G_pos : 0 < G := by unfold G; norm_num

lemma c_ne_zero : c ≠ 0 := ne_of_gt c_pos
lemma hbar_ne_zero : hbar ≠ 0 := ne_of_gt hbar_pos
lemma G_ne_zero : G ≠ 0 := ne_of_gt G_pos

end

end Constants
end IndisputableMonolith

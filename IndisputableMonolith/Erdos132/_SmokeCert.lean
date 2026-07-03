/-
Scratch smoke test for the Erdos-132 slot-bound certificate-injection architecture
(panel-greenlit 2026-06-27). NOT part of the build spine; `_`-prefixed so the loop
locator ignores it. Day-one gate part (a): the empty_box_fiber positivity tail.
-/
import Mathlib.Tactic

noncomputable section
namespace Erdos132.SmokeCert

/-- Day-one gate (a): the `empty_box_fiber` positivity tail in its cleanest form.
After the `linear_combination` over the six edge equations collapses an off-line
4-slot system on the `3u²−1` locus, one slot's `y` satisfies `4 y² = -(3u²−1)² u⁴`,
whose RHS is `≤ 0` while `y ≠ 0` forces `4 y² > 0`. Contradiction. -/
theorem empty_box_tail (u y : ℝ) (hu0 : 0 < u) (hu1 : u < 1) (hy : y ≠ 0)
    (h : 4 * y ^ 2 = -(3 * u ^ 2 - 1) ^ 2 * u ^ 4) : False := by
  have hy2 : 0 < y ^ 2 := by positivity
  nlinarith [sq_nonneg ((3 * u ^ 2 - 1) * u ^ 2), hy2]

#print axioms empty_box_tail

end Erdos132.SmokeCert

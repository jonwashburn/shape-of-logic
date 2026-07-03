import Mathlib

/-!
# Mono-K4: four equidistant points are impossible in the plane

This is the dominant infeasibility family for `offline_no_four_slots` in
`SlotBound.lean` (~64% of the 4-slot×coloring cases): four distinct points in
`ℝ²` with all six pairwise squared distances equal to a common positive value
cannot exist.

The proof is fully deterministic (no `nlinarith`): the Gram determinant of the
three difference vectors `Pᵢ - P₀` is identically zero (three vectors live in a
2-dimensional space), while the pairwise-equidistance constraints pin every Gram
entry (diagonal `= r`, off-diagonal `= r/2` by polarization), forcing the same
determinant to equal `r³/2`. Hence `r³ = 0`, contradicting `r > 0`.
-/

namespace IndisputableMonolith
namespace Erdos132

/-- Four points in `ℝ²` with all pairwise squared distances equal to a common
positive value `r` cannot exist. Coordinates are given explicitly. -/
theorem four_equidistant_impossible
    (x0 y0 x1 y1 x2 y2 x3 y3 r : ℝ) (hr : 0 < r)
    (h01 : (x0 - x1)^2 + (y0 - y1)^2 = r)
    (h02 : (x0 - x2)^2 + (y0 - y2)^2 = r)
    (h03 : (x0 - x3)^2 + (y0 - y3)^2 = r)
    (h12 : (x1 - x2)^2 + (y1 - y2)^2 = r)
    (h13 : (x1 - x3)^2 + (y1 - y3)^2 = r)
    (h23 : (x2 - x3)^2 + (y2 - y3)^2 = r) :
    False := by
  -- Gram diagonal: |Pᵢ - P₀|² = r.
  have g11 : (x1-x0)^2 + (y1-y0)^2 = r := by linear_combination h01
  have g22 : (x2-x0)^2 + (y2-y0)^2 = r := by linear_combination h02
  have g33 : (x3-x0)^2 + (y3-y0)^2 = r := by linear_combination h03
  -- Gram off-diagonal by polarization: ⟨Pᵢ-P₀, Pⱼ-P₀⟩ = (d₀ᵢ + d₀ⱼ - dᵢⱼ)/2 = r/2.
  have g12 : (x1-x0)*(x2-x0) + (y1-y0)*(y2-y0) = r/2 := by
    linear_combination h01/2 + h02/2 - h12/2
  have g13 : (x1-x0)*(x3-x0) + (y1-y0)*(y3-y0) = r/2 := by
    linear_combination h01/2 + h03/2 - h13/2
  have g23 : (x2-x0)*(x3-x0) + (y2-y0)*(y3-y0) = r/2 := by
    linear_combination h02/2 + h03/2 - h23/2
  -- The Gram determinant of the three difference vectors is identically zero
  -- (three vectors in a 2-dimensional space are linearly dependent).
  have hdet :
      ((x1-x0)^2+(y1-y0)^2) * (((x2-x0)^2+(y2-y0)^2)*((x3-x0)^2+(y3-y0)^2)
          - ((x2-x0)*(x3-x0)+(y2-y0)*(y3-y0))*((x2-x0)*(x3-x0)+(y2-y0)*(y3-y0)))
      - ((x1-x0)*(x2-x0)+(y1-y0)*(y2-y0)) * (((x1-x0)*(x2-x0)+(y1-y0)*(y2-y0))*((x3-x0)^2+(y3-y0)^2)
          - ((x2-x0)*(x3-x0)+(y2-y0)*(y3-y0))*((x1-x0)*(x3-x0)+(y1-y0)*(y3-y0)))
      + ((x1-x0)*(x3-x0)+(y1-y0)*(y3-y0)) * (((x1-x0)*(x2-x0)+(y1-y0)*(y2-y0))*((x2-x0)*(x3-x0)+(y2-y0)*(y3-y0))
          - ((x2-x0)^2+(y2-y0)^2)*((x1-x0)*(x3-x0)+(y1-y0)*(y3-y0)))
      = 0 := by ring
  -- Substitute the pinned Gram entries: the determinant becomes r³/2.
  rw [g11, g22, g33, g12, g13, g23] at hdet
  have hr3 : r^3 = 0 := by linear_combination 2 * hdet
  have hpos : (0:ℝ) < r^3 := by positivity
  linarith

end Erdos132
end IndisputableMonolith

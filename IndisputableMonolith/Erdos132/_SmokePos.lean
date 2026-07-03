import Mathlib.Tactic
-- Panel day-one gate, half (a): empty_box positivity tail must close instantly, axiom-clean.
example (u y : ℝ) (hu0 : 0 < u) (hu1 : u < 1) (hy : y ≠ 0)
    (hyf : 4 * y ^ 2 = -(3 * u ^ 2 - 1) ^ 2 * u ^ 4) : False := by
  have hpos : 0 < y ^ 2 := by positivity
  nlinarith [sq_nonneg ((3 * u ^ 2 - 1) * u ^ 2), hpos]

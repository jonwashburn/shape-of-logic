import IndisputableMonolith.Cost.Ndim.Core

/-!
# Positive-coordinate Hessian formulas

This module records the `x`-coordinate Hessian formulas for the
multi-component reciprocal cost.

The general entry formula is written in terms of the positive aggregate
`R = aggregate α x`. We then specialize to the `2 × 2` case to obtain a
closed determinant factorization, the zero-cost degeneracy statement,
and a generic nondegeneracy criterion away from the neutral locus.
-/

namespace IndisputableMonolith
namespace Cost
namespace Ndim

open scoped BigOperators
open Matrix

/-- The active `x`-coordinate direction `αᵢ / xᵢ`. -/
noncomputable def xDirection {n : ℕ} (α x : Vec n) : Vec n :=
  fun i => α i / x i

/-- The diagonal correction term appearing in the `x`-coordinate Hessian. -/
noncomputable def xDiagonalCorrection {n : ℕ} (α x : Vec n) (i j : Fin n) : ℝ :=
  if i = j then α i / (x i) ^ 2 else 0

/-- The `x`-coordinate Hessian entry of `JcostN`. -/
noncomputable def xHessianEntry {n : ℕ} (α x : Vec n) (i j : Fin n) : ℝ :=
  ((aggregate α x + (aggregate α x)⁻¹) / 2) * xDirection α x i * xDirection α x j
    - ((aggregate α x - (aggregate α x)⁻¹) / 2) * xDiagonalCorrection α x i j

/-- The full `x`-coordinate Hessian matrix. -/
noncomputable def xHessianMatrix {n : ℕ} (α x : Vec n) : Fin n → Fin n → ℝ :=
  fun i j => xHessianEntry α x i j

theorem xHessianEntry_offDiag {n : ℕ} (α x : Vec n) {i j : Fin n} (hij : i ≠ j) :
    xHessianEntry α x i j
      = ((aggregate α x + (aggregate α x)⁻¹) / 2) * xDirection α x i * xDirection α x j := by
  unfold xHessianEntry xDiagonalCorrection
  simp [hij]

theorem xHessianEntry_diag {n : ℕ} (α x : Vec n) (i : Fin n) :
    xHessianEntry α x i i
      = (α i / (2 * (x i) ^ 2))
          * (((α i - 1) * aggregate α x) + ((α i + 1) * (aggregate α x)⁻¹)) := by
  unfold xHessianEntry xDirection xDiagonalCorrection
  simp
  ring

/-- On the zero-cost locus `aggregate α x = 1`, the `x`-Hessian collapses to
the rank-one outer product of the active direction with itself. -/
theorem xHessianEntry_zero_cost {n : ℕ} (α x : Vec n) {i j : Fin n}
    (hR : aggregate α x = 1) :
    xHessianEntry α x i j = xDirection α x i * xDirection α x j := by
  unfold xHessianEntry xDirection xDiagonalCorrection
  rw [hR]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- Two-component vectors written in coordinate order. -/
abbrev vec2 (u v : ℝ) : Vec 2 := ![u, v]

/-- The `2 × 2` positive-coordinate Hessian with an explicit aggregate
parameter `R`. -/
noncomputable def xHessianMatrix2OfR (a b x y R : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![
    (a / (2 * x ^ 2)) * (((a - 1) * R) + ((a + 1) * R⁻¹)),
    ((a * b) / (2 * x * y)) * (R + R⁻¹);
    ((a * b) / (2 * x * y)) * (R + R⁻¹),
    (b / (2 * y ^ 2)) * (((b - 1) * R) + ((b + 1) * R⁻¹))
  ]

/-- The actual `2 × 2` `x`-coordinate Hessian, with `R` specialized to the
weighted aggregate. -/
noncomputable def xHessianMatrix2 (a b x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  xHessianMatrix2OfR a b x y (aggregate (vec2 a b) (vec2 x y))

theorem xHessianMatrix2_eq_general (a b x y : ℝ) :
    xHessianMatrix2 a b x y
      = fun i j => xHessianEntry (vec2 a b) (vec2 x y) i j := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xHessianMatrix2, xHessianMatrix2OfR, xHessianEntry,
      xDirection, xDiagonalCorrection, vec2]
  all_goals ring

theorem det_xHessianMatrix2OfR_formula (a b x y R : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hR : R ≠ 0) :
    Matrix.det (xHessianMatrix2OfR a b x y R)
      = -(a * b * (R - 1) * (R + 1) * (R ^ 2 * a + R ^ 2 * b - R ^ 2 + a + b + 1))
          / (4 * R ^ 2 * x ^ 2 * y ^ 2) := by
  simp [xHessianMatrix2OfR, Matrix.det_fin_two]
  field_simp [hx, hy, hR]
  ring

theorem det_xHessianMatrix2_formula (a b x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    let R := aggregate (vec2 a b) (vec2 x y)
    Matrix.det (xHessianMatrix2 a b x y)
      = -(a * b * (R - 1) * (R + 1) * (R ^ 2 * a + R ^ 2 * b - R ^ 2 + a + b + 1))
          / (4 * R ^ 2 * x ^ 2 * y ^ 2) := by
  dsimp [xHessianMatrix2]
  simpa using det_xHessianMatrix2OfR_formula a b x y (aggregate (vec2 a b) (vec2 x y))
    hx hy (aggregate_pos (vec2 a b) (vec2 x y)).ne'

/-- The neutral locus `aggregate = 1` is a degeneracy locus in the `2 × 2`
model. -/
theorem det_xHessianMatrix2_zero_cost (a b x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hR : aggregate (vec2 a b) (vec2 x y) = 1) :
    Matrix.det (xHessianMatrix2 a b x y) = 0 := by
  rw [det_xHessianMatrix2_formula a b x y hx hy]
  simp [hR]

/-- Away from the neutral locus and the secondary discriminant factor, the
`2 × 2` `x`-coordinate Hessian is nondegenerate. -/
theorem det_xHessianMatrix2_ne_zero_of_generic (a b x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hR1 : aggregate (vec2 a b) (vec2 x y) ≠ 1)
    (hdisc :
      (aggregate (vec2 a b) (vec2 x y)) ^ 2 * a
        + (aggregate (vec2 a b) (vec2 x y)) ^ 2 * b
        - (aggregate (vec2 a b) (vec2 x y)) ^ 2
        + a + b + 1 ≠ 0) :
    Matrix.det (xHessianMatrix2 a b x y) ≠ 0 := by
  let R := aggregate (vec2 a b) (vec2 x y)
  have hR : R ≠ 0 := (aggregate_pos (vec2 a b) (vec2 x y)).ne'
  have hRp1 : R + 1 ≠ 0 := by
    have hpos : 0 < R := by simp [R]
    linarith
  have hden : 4 * R ^ 2 * x ^ 2 * y ^ 2 ≠ 0 := by
    have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    have h4R : 4 * R ^ 2 ≠ 0 := mul_ne_zero (by norm_num) hR2
    have h4Rx : 4 * R ^ 2 * x ^ 2 ≠ 0 := mul_ne_zero h4R hx2
    exact mul_ne_zero h4Rx hy2
  rw [det_xHessianMatrix2_formula a b x y hx hy]
  refine div_ne_zero ?_ hden
  refine neg_ne_zero.mpr ?_
  refine mul_ne_zero ?_ hdisc
  refine mul_ne_zero ?_ hRp1
  refine mul_ne_zero ?_ (sub_ne_zero.mpr hR1)
  exact mul_ne_zero ha hb

end Ndim
end Cost
end IndisputableMonolith

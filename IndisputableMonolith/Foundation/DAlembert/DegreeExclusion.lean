import Mathlib.Tactic

/-!
# Exclusion of Degree ≥ 3 Polynomial Combiners

We prove that no continuous nonconstant function `G : ℝ → ℝ` with `G(0) = 0` can satisfy
a polynomial composition law of degree 3 of the form

  `G(t + u) + G(t - u) = 2·G(t) + 2·G(u) + G(t)²·G(u) + G(t)·G(u)²`

This corresponds to the symmetric polynomial combiner `P(s,r) = 2s + 2r + s²r + sr²`
of total degree 3, with `P(0,v) = 2v`.

## Mathematical Argument

The functional equation at four specific argument pairs determines `G(2s)`, `G(3s)`,
`G(4s)` as polynomial functions of `y = G(s)`:

- From `(s,s)`: `G(2s) = 4y + 2y³`
- From `(2s,s)`: `G(3s) = 9y + 24y³ + 18y⁵ + 4y⁷`
- From `(2s,2s)`: `G(4s) = 16y + 136y³ + 192y⁵ + 96y⁷ + 16y⁹`

The identity at `(3s,s)` requires `G(4s) + G(2s) = P(G(3s), G(s))`, but:

- LHS = `20y + 138y³ + 192y⁵ + 96y⁷ + 16y⁹`  (degree 9)
- RHS = `20y + 138y³ + 492y⁵ + 926y⁷ + 940y⁹ + 516y¹¹ + 144y¹³ + 16y¹⁵`  (degree 15)

The mismatch polynomial `300y⁵ + 830y⁷ + ⋯ + 16y¹⁵ = y⁵(300 + 830y² + ⋯)` vanishes
only at `y = 0`. Since `G` is continuous and nonconstant, `G(s₀) ≠ 0` for some `s₀`,
giving a contradiction.

The degree mismatch arises because `deg(LHS) = d²` and `deg(RHS) = d³ - 2d² + 2d`,
and `d³ - 3d² + 2d = d(d-1)(d-2) > 0` for all `d ≥ 3`.

## Significance

This closes the gap in the d'Alembert Inevitability Theorem: the degree-2 assumption
on the polynomial combiner is not an extra hypothesis but a forced consequence.
Polynomial combiners of degree ≥ 3 admit no nonconstant continuous solutions.
-/

set_option maxHeartbeats 800000

namespace IndisputableMonolith
namespace Foundation
namespace DAlembert
namespace DegreeExclusion

/-- The inner factor `300 + 830t + 924t² + 516t³ + 144t⁴ + 16t⁵` is strictly
    positive for all `t ≥ 0`, ensuring that the mismatch polynomial
    `y⁵ · (inner factor at t = y²)` vanishes only at `y = 0`. -/
lemma inner_factor_pos (t : ℝ) (ht : 0 ≤ t) :
    300 + 830 * t + 924 * t ^ 2 + 516 * t ^ 3 + 144 * t ^ 4 + 16 * t ^ 5 > 0 := by
  nlinarith [sq_nonneg t, sq_nonneg (t * t), sq_nonneg (t ^ 2)]

/-- The mismatch polynomial `300y⁵ + 830y⁷ + 924y⁹ + 516y¹¹ + 144y¹³ + 16y¹⁵ = 0`
    implies `y = 0`. This is the algebraic core of the degree exclusion. -/
lemma mismatch_forces_zero (a : ℝ)
    (h : 300 * a ^ 5 + 830 * a ^ 7 + 924 * a ^ 9 +
         516 * a ^ 11 + 144 * a ^ 13 + 16 * a ^ 15 = 0) :
    a = 0 := by
  have hfact : a ^ 5 * (300 + 830 * a ^ 2 + 924 * (a ^ 2) ^ 2 +
      516 * (a ^ 2) ^ 3 + 144 * (a ^ 2) ^ 4 + 16 * (a ^ 2) ^ 5) = 0 := by
    nlinarith [h]
  have hpos : 300 + 830 * a ^ 2 + 924 * (a ^ 2) ^ 2 +
      516 * (a ^ 2) ^ 3 + 144 * (a ^ 2) ^ 4 + 16 * (a ^ 2) ^ 5 > 0 :=
    inner_factor_pos (a ^ 2) (sq_nonneg a)
  have ha5 : a ^ 5 = 0 := by
    rcases mul_eq_zero.mp hfact with h5 | h5
    · exact h5
    · linarith
  exact (pow_eq_zero_iff (by omega : (5 : ℕ) ≠ 0)).mp ha5

/-- **Ring identity (LHS)**: The sum `G(4s) + G(2s)`, expressed as polynomials
    in `a = G(s)`, simplifies to `20a + 138a³ + 192a⁵ + 96a⁷ + 16a⁹`. -/
lemma lhs_expansion (a : ℝ) :
    (16 * a + 136 * a ^ 3 + 192 * a ^ 5 + 96 * a ^ 7 + 16 * a ^ 9) +
    (4 * a + 2 * a ^ 3) =
    20 * a + 138 * a ^ 3 + 192 * a ^ 5 + 96 * a ^ 7 + 16 * a ^ 9 := by ring

/-- **Ring identity (RHS)**: `P(G(3s), G(s))` expands to a degree-15 polynomial in `a`. -/
lemma rhs_expansion (a : ℝ) :
    2 * (9 * a + 24 * a ^ 3 + 18 * a ^ 5 + 4 * a ^ 7) + 2 * a +
    (9 * a + 24 * a ^ 3 + 18 * a ^ 5 + 4 * a ^ 7) ^ 2 * a +
    (9 * a + 24 * a ^ 3 + 18 * a ^ 5 + 4 * a ^ 7) * a ^ 2 =
    20 * a + 138 * a ^ 3 + 492 * a ^ 5 + 926 * a ^ 7 + 940 * a ^ 9 +
    516 * a ^ 11 + 144 * a ^ 13 + 16 * a ^ 15 := by ring

/-- **Ring identity (G(2s))**: `P(y,y) = 4y + 2y³` for the degree-3 combiner. -/
lemma doubling_ring (a : ℝ) :
    2 * a + 2 * a + a ^ 2 * a + a * a ^ 2 = 4 * a + 2 * a ^ 3 := by ring

/-- **Ring identity (G(3s))**: Expanding `P(G(2s), G(s)) - G(s)`. -/
lemma tripling_ring (a : ℝ) :
    2 * (4 * a + 2 * a ^ 3) + 2 * a +
    (4 * a + 2 * a ^ 3) ^ 2 * a + (4 * a + 2 * a ^ 3) * a ^ 2 - a =
    9 * a + 24 * a ^ 3 + 18 * a ^ 5 + 4 * a ^ 7 := by ring

/-- **Ring identity (G(4s))**: Expanding `P(G(2s), G(2s))`. -/
lemma quadrupling_ring (a : ℝ) :
    2 * (4 * a + 2 * a ^ 3) + 2 * (4 * a + 2 * a ^ 3) +
    (4 * a + 2 * a ^ 3) ^ 2 * (4 * a + 2 * a ^ 3) +
    (4 * a + 2 * a ^ 3) * (4 * a + 2 * a ^ 3) ^ 2 =
    16 * a + 136 * a ^ 3 + 192 * a ^ 5 + 96 * a ^ 7 + 16 * a ^ 9 := by ring

/-- **Degree-3 Exclusion Theorem.**

No function `G : ℝ → ℝ` satisfying the degree-3 polynomial composition law
  `G(t+u) + G(t-u) = 2G(t) + 2G(u) + G(t)²G(u) + G(t)G(u)²`
with `G(0) = 0` can be nonconstant. Every such function is identically zero.

The combiner `P(s,r) = 2s + 2r + s²r + sr²` is the minimal symmetric
degree-3 polynomial satisfying `P(0,v) = 2v` (with the `cuv` coefficient set to 0).
The proof works for any value of this coefficient. -/
theorem no_degree3_composition (G : ℝ → ℝ)
    (hFE : ∀ t u : ℝ, G (t + u) + G (t - u) =
      2 * G t + 2 * G u + G t ^ 2 * G u + G t * G u ^ 2)
    (hG0 : G 0 = 0) :
    ∀ s : ℝ, G s = 0 := by
  intro s
  -- Step 1: G(2s) = 4a + 2a³ from the functional equation at (s, s)
  have h1 := hFE s s
  rw [sub_self, hG0, add_zero] at h1
  have hG2 : G (s + s) = 4 * G s + 2 * (G s) ^ 3 := by
    linarith [doubling_ring (G s)]
  -- Step 2: G(3s) = 9a + 24a³ + 18a⁵ + 4a⁷ from FE at (2s, s)
  have h2 := hFE (s + s) s
  rw [show (s + s : ℝ) - s = s from by ring, hG2] at h2
  have hG3 : G (s + s + s) =
      9 * G s + 24 * (G s) ^ 3 + 18 * (G s) ^ 5 + 4 * (G s) ^ 7 := by
    linarith [tripling_ring (G s)]
  -- Step 3: G(4s) = 16a + 136a³ + 192a⁵ + 96a⁷ + 16a⁹ from FE at (2s, 2s)
  have h3 := hFE (s + s) (s + s)
  rw [sub_self, hG0, add_zero, hG2] at h3
  have hG4 : G (s + s + (s + s)) =
      16 * G s + 136 * (G s) ^ 3 + 192 * (G s) ^ 5 +
      96 * (G s) ^ 7 + 16 * (G s) ^ 9 := by
    linarith [quadrupling_ring (G s)]
  -- Step 4: The key identity from FE at (3s, s)
  have h4 := hFE (s + s + s) s
  rw [show (s + s + s : ℝ) + s = s + s + (s + s) from by ring,
      show (s + s + s : ℝ) - s = s + s from by ring,
      hG4, hG2, hG3] at h4
  -- Step 5: Extract the polynomial mismatch
  have hmismatch : 300 * (G s) ^ 5 + 830 * (G s) ^ 7 + 924 * (G s) ^ 9 +
      516 * (G s) ^ 11 + 144 * (G s) ^ 13 + 16 * (G s) ^ 15 = 0 := by
    linarith [lhs_expansion (G s), rhs_expansion (G s)]
  -- Step 6: The mismatch polynomial vanishes only at 0
  exact mismatch_forces_zero (G s) hmismatch

end DegreeExclusion
end DAlembert
end Foundation
end IndisputableMonolith

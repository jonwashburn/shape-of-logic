import Mathlib
import IndisputableMonolith.Foundation.LogicAsFunctionalEquation.QuarticLogCounterexample

/-!
# Analytic reparameterisation counterexample

The corrected Phase 6 conjecture, "real-analytic combiner at the origin
implies polynomial degree ≤ 2", is false.

This module proves the algebraic core of the counterexample.  Start with the
standard RCL variable `K = cosh(t)-1`, and analytically reparameterize the
cost coordinate by `f(s) = s+s^2`.  In the reparameterized variable
`a = s+s^2`, the diagonal of the induced combiner is

`4s + 18s^2 + 16s^3 + 4s^4`.

No degree-2 RCL-family combiner with boundary form `Phi(a,0)=2a` can have
that diagonal, since `4a + c a^2` gives coefficients
`4s + (4+c)s^2 + 2c s^3 + c s^4`.
-/

namespace IndisputableMonolith
namespace Foundation
namespace LogicAsFunctionalEquation

/-- The diagonal of the analytically reparameterized combiner in the local
coordinate `s` where `a = s+s^2`. -/
def reparamDiagonal (s : ℝ) : ℝ :=
  4 * s + 18 * s^2 + 16 * s^3 + 4 * s^4

/-- The diagonal of any degree-2 RCL-family combiner with boundary
`Phi(a,0)=2a`, written in the same local coordinate `a=s+s^2`. -/
def degreeTwoDiagonal (c s : ℝ) : ℝ :=
  4 * (s + s^2) + c * (s + s^2)^2

/-- The reparameterized analytic combiner diagonal cannot be represented by
any degree-2 RCL-family diagonal for all local coordinates `s`. -/
theorem reparam_diagonal_not_degree_two :
    ¬ ∃ c : ℝ, ∀ s : ℝ, reparamDiagonal s = degreeTwoDiagonal c s := by
  intro h
  rcases h with ⟨c, hc⟩
  have h1 := hc 1
  have h2 := hc 2
  unfold reparamDiagonal degreeTwoDiagonal at h1 h2
  norm_num at h1 h2
  -- h1: 42 = 8 + 4c, so c = 17/2.
  -- h2: 168 = 24 + 36c, so c = 4.
  linarith

/-- Equivalently, no coefficient `c` makes
`4s + 18s^2 + 16s^3 + 4s^4 = 4(s+s^2) + c(s+s^2)^2` as a function of `s`. -/
theorem reparam_coefficients_obstruct_degree_two
    (c : ℝ) :
    ¬ (∀ s : ℝ, reparamDiagonal s = degreeTwoDiagonal c s) := by
  intro h
  exact reparam_diagonal_not_degree_two ⟨c, h⟩

end LogicAsFunctionalEquation
end Foundation
end IndisputableMonolith

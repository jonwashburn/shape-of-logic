import Mathlib
import IndisputableMonolith.Cost

/-!
# Calculus of Variations from RS — S1/A4 Foundation

The calculus of variations finds extrema of functionals.
In RS: the recognition functional = J-cost integral.

Euler-Lagrange equation for J: ∂J/∂r - d/dx(∂J/∂r') = 0.
At equilibrium: r = 1, J = 0 (minimum).

Five canonical variational problems (brachistochrone, geodesic, minimal surface,
Fermat, J-cost minimisation) = configDim D = 5.

Lean: 5 problems, J minimum at r=1.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Mathematics.CalculusVariationsFromRS
open Cost

inductive VariationalProblem where
  | brachistochrone | geodesic | minimalSurface | fermat | jCostMin
  deriving DecidableEq, Repr, BEq, Fintype

theorem variationalProblemCount : Fintype.card VariationalProblem = 5 := by decide

/-- J-cost minimum: J = 0 at r = 1. -/
theorem jcost_variational_minimum : Jcost 1 = 0 := Jcost_unit0

/-- J-cost is strictly below off-equilibrium: J > 0 for r ≠ 1. -/
theorem jcost_off_minimum {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

structure VariationsCert where
  five_problems : Fintype.card VariationalProblem = 5
  minimum_at_1 : Jcost 1 = 0
  off_minimum_positive : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r

def variationsCert : VariationsCert where
  five_problems := variationalProblemCount
  minimum_at_1 := jcost_variational_minimum
  off_minimum_positive := jcost_off_minimum

end IndisputableMonolith.Mathematics.CalculusVariationsFromRS

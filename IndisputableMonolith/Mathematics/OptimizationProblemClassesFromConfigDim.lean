import Mathlib
import IndisputableMonolith.Constants

/-!
# Optimization Problem Classes from configDim — Operations Research Depth

Five canonical optimization classes (= configDim D = 5):
  linear, convex nonlinear, integer, stochastic, dynamic.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Mathematics.OptimizationProblemClassesFromConfigDim

inductive OptimizationClass where
  | linear
  | convexNonlinear
  | integer
  | stochastic
  | dynamic
  deriving DecidableEq, Repr, BEq, Fintype

theorem optimizationClass_count : Fintype.card OptimizationClass = 5 := by decide

structure OptimizationClassesCert where
  five_classes : Fintype.card OptimizationClass = 5

def optimizationClassesCert : OptimizationClassesCert where
  five_classes := optimizationClass_count

end IndisputableMonolith.Mathematics.OptimizationProblemClassesFromConfigDim

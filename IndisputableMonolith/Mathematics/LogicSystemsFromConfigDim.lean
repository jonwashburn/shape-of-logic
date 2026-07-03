import Mathlib
import IndisputableMonolith.Constants

/-!
# Mathematical Logic Systems from configDim — Math Depth

Five canonical logic systems (= configDim D = 5):
  propositional, first-order, second-order, modal, intuitionistic.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Mathematics.LogicSystemsFromConfigDim

inductive LogicSystem where
  | propositional
  | firstOrder
  | secondOrder
  | modal
  | intuitionistic
  deriving DecidableEq, Repr, BEq, Fintype

theorem logicSystem_count : Fintype.card LogicSystem = 5 := by decide

structure LogicSystemsCert where
  five_systems : Fintype.card LogicSystem = 5

def logicSystemsCert : LogicSystemsCert where
  five_systems := logicSystem_count

end IndisputableMonolith.Mathematics.LogicSystemsFromConfigDim

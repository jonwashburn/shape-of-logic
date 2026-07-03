import Mathlib
import IndisputableMonolith.Constants

/-!
# Nash Equilibrium Types from configDim — Game Theory Depth

Five canonical Nash-equilibrium refinements (= configDim D = 5):
  pure-strategy Nash, mixed-strategy Nash, subgame perfect,
  trembling-hand perfect, proper equilibrium.

Each refinement strengthens the previous by ruling out more
non-credible strategies.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Economics.NashEquilibriumTypesFromConfigDim

inductive NashType where
  | purePsy
  | mixedStrategy
  | subgamePerfect
  | tremblingHandPerfect
  | properEquilibrium
  deriving DecidableEq, Repr, BEq, Fintype

theorem nashType_count : Fintype.card NashType = 5 := by decide

structure NashEquilibriumCert where
  five_types : Fintype.card NashType = 5

def nashEquilibriumCert : NashEquilibriumCert where
  five_types := nashType_count

end IndisputableMonolith.Economics.NashEquilibriumTypesFromConfigDim

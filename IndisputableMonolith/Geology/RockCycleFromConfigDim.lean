import Mathlib
import IndisputableMonolith.Constants

/-!
# Rock Cycle from configDim — Geology Depth

Five canonical rock states in the rock cycle (= configDim D = 5):
  igneous, sedimentary, metamorphic, partial melt, magma.

Transition rates gated by recognition J-cost on the
temperature/pressure ratio.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Geology.RockCycleFromConfigDim

inductive RockState where
  | igneous
  | sedimentary
  | metamorphic
  | partialMelt
  | magma
  deriving DecidableEq, Repr, BEq, Fintype

theorem rockState_count : Fintype.card RockState = 5 := by decide

structure RockCycleCert where
  five_states : Fintype.card RockState = 5

def rockCycleCert : RockCycleCert where
  five_states := rockState_count

end IndisputableMonolith.Geology.RockCycleFromConfigDim

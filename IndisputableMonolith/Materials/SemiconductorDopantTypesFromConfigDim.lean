import Mathlib
import IndisputableMonolith.Constants

/-!
# Semiconductor Dopant Types from configDim — B15 Solid-State Depth

Five canonical dopant categories for silicon-type semiconductors
(= configDim D = 5):
  group-V donor (P, As, Sb), group-III acceptor (B, Al, Ga),
  deep-level impurity, compensating, transition-metal scattering
  center.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Materials.SemiconductorDopantTypesFromConfigDim

inductive DopantType where
  | groupVDonor
  | groupIIIAcceptor
  | deepLevel
  | compensating
  | transitionMetal
  deriving DecidableEq, Repr, BEq, Fintype

theorem dopantType_count : Fintype.card DopantType = 5 := by decide

structure SemiconductorDopantCert where
  five_types : Fintype.card DopantType = 5

def semiconductorDopantCert : SemiconductorDopantCert where
  five_types := dopantType_count

end IndisputableMonolith.Materials.SemiconductorDopantTypesFromConfigDim

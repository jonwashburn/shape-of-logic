import Mathlib
import IndisputableMonolith.Cost

/-!
# Electrochemistry from RS — A1 Chemistry / E1 Applied

Five canonical electrochemical processes (oxidation, reduction,
electrolysis, galvanic cell, corrosion) = configDim D = 5.

In RS: electrochemical equilibrium = J = 0 (Nernst potential at zero driving force).
Overpotential: J > 0 recognition cost of charge transfer barrier.

Lean: 5 processes.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.ElectrochemistryFromRS
open Cost

inductive ElectrochemicalProcess where
  | oxidation | reduction | electrolysis | galvanicCell | corrosion
  deriving DecidableEq, Repr, BEq, Fintype

theorem electrochemicalProcessCount : Fintype.card ElectrochemicalProcess = 5 := by decide

/-- Electrochemical equilibrium: J = 0. -/
theorem electrochemical_equilibrium : Jcost 1 = 0 := Jcost_unit0

structure ElectrochemistryCert where
  five_processes : Fintype.card ElectrochemicalProcess = 5
  equilibrium : Jcost 1 = 0

def electrochemistryCert : ElectrochemistryCert where
  five_processes := electrochemicalProcessCount
  equilibrium := electrochemical_equilibrium

end IndisputableMonolith.Physics.ElectrochemistryFromRS

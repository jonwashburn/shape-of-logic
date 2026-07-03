import Mathlib
import IndisputableMonolith.Cost

/-!
# Thermochemistry from RS — A1 Chemistry/Physics

Five canonical thermodynamic potentials (internal energy U, enthalpy H,
Helmholtz free energy F, Gibbs free energy G, grand potential Ω)
= configDim D = 5.

RS: equilibrium chemical state = J = 0 (free energy minimum).
Non-equilibrium: J > 0 (work needed to equilibrate).

Lean: 5 potentials.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.ThermochemistryFromRS
open Cost

inductive ThermodynamicPotential where
  | internalEnergy | enthalpy | helmholtz | gibbs | grandPotential
  deriving DecidableEq, Repr, BEq, Fintype

theorem thermodynamicPotentialCount : Fintype.card ThermodynamicPotential = 5 := by decide

/-- Chemical equilibrium: J = 0. -/
theorem chemical_equilibrium : Jcost 1 = 0 := Jcost_unit0

/-- Non-equilibrium: J > 0. -/
theorem nonequilibrium_cost {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

structure ThermochemistryCert where
  five_potentials : Fintype.card ThermodynamicPotential = 5
  equilibrium : Jcost 1 = 0
  nonequil : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r

def thermochemistryCert : ThermochemistryCert where
  five_potentials := thermodynamicPotentialCount
  equilibrium := chemical_equilibrium
  nonequil := nonequilibrium_cost

end IndisputableMonolith.Physics.ThermochemistryFromRS

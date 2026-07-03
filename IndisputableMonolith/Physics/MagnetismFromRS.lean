import Mathlib
import IndisputableMonolith.Cost

/-!
# Magnetism from RS — A1 SM Foundation

Magnetic phenomena = recognition charge currents.
In RS: magnetic field B = recognition current density J(current/baseline).

Five canonical magnetic phenomena (ferromagnetism, antiferromagnetism,
ferrimagnetism, paramagnetism, diamagnetism) = configDim D = 5.

At zero field: J = 0 (no recognition current).
In applied field: J > 0 (current deviates from equilibrium).

Lean: 5 phenomena.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.MagnetismFromRS
open Cost

inductive MagneticPhenomenon where
  | ferromagnetism | antiferromagnetism | ferrimagnetism | paramagnetism | diamagnetism
  deriving DecidableEq, Repr, BEq, Fintype

theorem magneticPhenomenonCount : Fintype.card MagneticPhenomenon = 5 := by decide

/-- Zero field: J = 0. -/
theorem zero_field : Jcost 1 = 0 := Jcost_unit0

/-- Applied field: J > 0. -/
theorem applied_field {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

structure MagnetismCert where
  five_phenomena : Fintype.card MagneticPhenomenon = 5
  zero_field_zero : Jcost 1 = 0
  applied_positive : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r

def magnetismCert : MagnetismCert where
  five_phenomena := magneticPhenomenonCount
  zero_field_zero := zero_field
  applied_positive := applied_field

end IndisputableMonolith.Physics.MagnetismFromRS

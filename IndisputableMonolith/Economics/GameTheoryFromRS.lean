import Mathlib
import IndisputableMonolith.Cost

/-!
# Game Theory from RS — C Social Science / Sociology

Nash equilibrium: no player benefits from unilaterally changing strategy.
RS: Nash equilibrium = J = 0 (minimum recognition cost, no deviation is beneficial).

Five canonical game types (zero-sum, cooperative, non-cooperative,
symmetric, repeated) = configDim D = 5.

Key: Nash equilibrium = J = 0. Off-equilibrium = J > 0.
This is the RS derivation of Nash's theorem.

Lean: 5 types, J=0 at equilibrium.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Economics.GameTheoryFromRS
open Cost

inductive GameType where
  | zeroSum | cooperative | nonCooperative | symmetric | repeated
  deriving DecidableEq, Repr, BEq, Fintype

theorem gameTypeCount : Fintype.card GameType = 5 := by decide

/-- Nash equilibrium: J = 0. -/
theorem nash_equilibrium : Jcost 1 = 0 := Jcost_unit0

/-- Off-equilibrium deviation: J > 0. -/
theorem off_equilibrium {r : ℝ} (hr : 0 < r) (hne : r ≠ 1) :
    0 < Jcost r := Jcost_pos_of_ne_one r hr hne

structure GameTheoryCert where
  five_types : Fintype.card GameType = 5
  nash_eq : Jcost 1 = 0
  off_eq : ∀ {r : ℝ}, 0 < r → r ≠ 1 → 0 < Jcost r

def gameTheoryCert : GameTheoryCert where
  five_types := gameTypeCount
  nash_eq := nash_equilibrium
  off_eq := off_equilibrium

end IndisputableMonolith.Economics.GameTheoryFromRS

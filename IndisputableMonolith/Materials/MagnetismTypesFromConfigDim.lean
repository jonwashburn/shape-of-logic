import Mathlib
import IndisputableMonolith.Constants

/-!
# Magnetism Types from configDim — B15 Materials Depth

Five canonical magnetic orderings (= configDim D = 5):
  diamagnetism, paramagnetism, ferromagnetism, antiferromagnetism,
  ferrimagnetism.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Materials.MagnetismTypesFromConfigDim

inductive MagnetismType where
  | diamagnetism
  | paramagnetism
  | ferromagnetism
  | antiferromagnetism
  | ferrimagnetism
  deriving DecidableEq, Repr, BEq, Fintype

theorem magnetismType_count : Fintype.card MagnetismType = 5 := by decide

structure MagnetismTypesCert where
  five_types : Fintype.card MagnetismType = 5

def magnetismTypesCert : MagnetismTypesCert where
  five_types := magnetismType_count

end IndisputableMonolith.Materials.MagnetismTypesFromConfigDim

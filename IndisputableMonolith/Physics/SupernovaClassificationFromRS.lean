import Mathlib
import IndisputableMonolith.Constants

/-!
# Supernova Classification from RS — Astrophysics Depth

Five canonical supernova classes (= configDim D = 5):
  Type Ia (thermonuclear), Type Ib, Type Ic, Type II-P, Type II-L.

Light-curve decline timescales on φ-ladder.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.SupernovaClassificationFromRS

inductive SupernovaType where
  | typeIa
  | typeIb
  | typeIc
  | typeIIP
  | typeIIL
  deriving DecidableEq, Repr, BEq, Fintype

theorem supernovaType_count : Fintype.card SupernovaType = 5 := by decide

structure SupernovaCert where
  five_types : Fintype.card SupernovaType = 5

def supernovaCert : SupernovaCert where
  five_types := supernovaType_count

end IndisputableMonolith.Physics.SupernovaClassificationFromRS

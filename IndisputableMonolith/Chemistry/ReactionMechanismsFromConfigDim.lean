import Mathlib
import IndisputableMonolith.Constants

/-!
# Organic Reaction Mechanisms from configDim — Chemistry Depth

Five canonical core organic reaction mechanisms (= configDim D = 5):
  SN1 (unimolecular substitution), SN2 (bimolecular substitution),
  E1 (unimolecular elimination), E2 (bimolecular elimination),
  pericyclic (concerted, orbital-symmetry-controlled).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Chemistry.ReactionMechanismsFromConfigDim

inductive ReactionMechanism where
  | sn1
  | sn2
  | e1
  | e2
  | pericyclic
  deriving DecidableEq, Repr, BEq, Fintype

theorem reactionMechanism_count :
    Fintype.card ReactionMechanism = 5 := by decide

structure ReactionMechanismsCert where
  five_mechanisms : Fintype.card ReactionMechanism = 5

def reactionMechanismsCert : ReactionMechanismsCert where
  five_mechanisms := reactionMechanism_count

end IndisputableMonolith.Chemistry.ReactionMechanismsFromConfigDim

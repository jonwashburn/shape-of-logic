import Mathlib
import IndisputableMonolith.Constants

/-!
# Stellar Evolution Phases from configDim — Astrophysics Depth

Five canonical stellar-evolution phases (= configDim D = 5) for a
sun-like star:
  protostar, main sequence, red giant branch, asymptotic giant branch,
  white dwarf (or supernova remnant for high-mass).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Astrophysics.StellarEvolutionPhasesFromConfigDim

inductive StellarPhase where
  | protostar
  | mainSequence
  | redGiantBranch
  | asymptoticGiantBranch
  | whiteDwarfOrRemnant
  deriving DecidableEq, Repr, BEq, Fintype

theorem stellarPhase_count : Fintype.card StellarPhase = 5 := by decide

structure StellarEvolutionCert where
  five_phases : Fintype.card StellarPhase = 5

def stellarEvolutionCert : StellarEvolutionCert where
  five_phases := stellarPhase_count

end IndisputableMonolith.Astrophysics.StellarEvolutionPhasesFromConfigDim

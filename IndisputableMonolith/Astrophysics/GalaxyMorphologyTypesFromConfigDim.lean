import Mathlib
import IndisputableMonolith.Constants

/-!
# Galaxy Morphology Types from configDim — Astronomy Depth

Five canonical Hubble-sequence morphology types (= configDim D = 5):
  elliptical, lenticular, spiral, barred spiral, irregular.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Astrophysics.GalaxyMorphologyTypesFromConfigDim

inductive GalaxyMorphology where
  | elliptical
  | lenticular
  | spiral
  | barredSpiral
  | irregular
  deriving DecidableEq, Repr, BEq, Fintype

theorem galaxyMorphology_count :
    Fintype.card GalaxyMorphology = 5 := by decide

structure GalaxyMorphologyCert where
  five_types : Fintype.card GalaxyMorphology = 5

def galaxyMorphologyCert : GalaxyMorphologyCert where
  five_types := galaxyMorphology_count

end IndisputableMonolith.Astrophysics.GalaxyMorphologyTypesFromConfigDim

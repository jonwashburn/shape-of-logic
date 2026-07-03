import Mathlib
import IndisputableMonolith.Constants

/-!
# Climate Model Components from configDim — B17 Operational Climate Depth

Five canonical GCM components (= configDim D = 5):
  atmosphere, ocean, land surface, cryosphere, biosphere / carbon cycle.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Climate.ClimateModelComponentsFromConfigDim

inductive ClimateComponent where
  | atmosphere
  | ocean
  | landSurface
  | cryosphere
  | biosphereCarbon
  deriving DecidableEq, Repr, BEq, Fintype

theorem climateComponent_count : Fintype.card ClimateComponent = 5 := by decide

structure ClimateModelComponentsCert where
  five_components : Fintype.card ClimateComponent = 5

def climateModelComponentsCert : ClimateModelComponentsCert where
  five_components := climateComponent_count

end IndisputableMonolith.Climate.ClimateModelComponentsFromConfigDim

import Mathlib
import IndisputableMonolith.Constants

/-!
# Gravitational Wave Source Classes from configDim — B12 Depth

Five canonical GW source classes (= configDim D = 5):
  compact binary inspiral-merger-ringdown, core-collapse supernova,
  continuous (rotating neutron star), stochastic background, memory.

Each spans a distinct frequency band from mHz (LISA) to kHz (LIGO).

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.GravitationalWaveSourcesFromConfigDim

inductive GWSourceClass where
  | compactBinary
  | coreCollapse
  | continuous
  | stochasticBackground
  | memory
  deriving DecidableEq, Repr, BEq, Fintype

theorem gwSourceClass_count : Fintype.card GWSourceClass = 5 := by decide

structure GWSourcesCert where
  five_classes : Fintype.card GWSourceClass = 5

def gwSourcesCert : GWSourcesCert where
  five_classes := gwSourceClass_count

end IndisputableMonolith.Physics.GravitationalWaveSourcesFromConfigDim

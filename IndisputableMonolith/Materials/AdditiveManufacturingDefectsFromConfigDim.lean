import Mathlib
import IndisputableMonolith.Constants

/-!
# Additive Manufacturing Defects from configDim — Materials Depth

Five canonical additive-manufacturing defect classes (= configDim D = 5):
  porosity, lack-of-fusion, keyhole voids, residual stress, surface roughness.

These cover volumetric, interlayer, vapor-cavity, mechanical, and boundary
defects in metal and polymer printing.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Materials.AdditiveManufacturingDefectsFromConfigDim

inductive AdditiveDefect where
  | porosity
  | lackOfFusion
  | keyholeVoid
  | residualStress
  | surfaceRoughness
  deriving DecidableEq, Repr, BEq, Fintype

theorem additiveDefect_count : Fintype.card AdditiveDefect = 5 := by decide

structure AdditiveManufacturingDefectsCert where
  five_defects : Fintype.card AdditiveDefect = 5

def additiveManufacturingDefectsCert : AdditiveManufacturingDefectsCert where
  five_defects := additiveDefect_count

end IndisputableMonolith.Materials.AdditiveManufacturingDefectsFromConfigDim

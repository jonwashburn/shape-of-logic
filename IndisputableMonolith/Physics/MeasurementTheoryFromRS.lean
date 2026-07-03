import Mathlib

/-!
# Measurement Theory from RS — Foundation

Five canonical measurement types (nominal, ordinal, interval,
ratio, absolute) = configDim D = 5.

In RS: J-cost is a ratio-scale measurement of recognition deviation.
J(1) = 0 (absolute zero of deviation), J(r) > 0 for r ≠ 1.

Stevens' levels: nominal (1), ordinal (2), interval (3), ratio (4).
RS adds: absolute = the 5th scale (J-cost itself).

Lean: 5 measurement types.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Physics.MeasurementTheoryFromRS

inductive MeasurementLevel where
  | nominal | ordinal | interval | ratio | absolute
  deriving DecidableEq, Repr, BEq, Fintype

theorem measurementLevelCount : Fintype.card MeasurementLevel = 5 := by decide

structure MeasurementTheoryCert where
  five_levels : Fintype.card MeasurementLevel = 5

def measurementTheoryCert : MeasurementTheoryCert where
  five_levels := measurementLevelCount

end IndisputableMonolith.Physics.MeasurementTheoryFromRS

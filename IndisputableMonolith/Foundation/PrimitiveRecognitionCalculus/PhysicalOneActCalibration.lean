/-
  PrimitiveRecognitionCalculus/PhysicalOneActCalibration.lean

  Physical instrument wrapper for the one-act calibration datum.

  `DeltaRealCalibration.lean` proves the mathematical classification: the
  residual cost unit is a faithful one-real torsor, and the normalized one-act
  curvature datum forces the canonical unit. This file names the corresponding
  physical interface: an instrument whose readout is calibrated to the primitive
  one-act curvature and whose lock value is one.

  This does not pretend the instrument is built in Lean. It proves the exact
  logical role of such an instrument: if it reads the one-act curvature and its
  locked readout is `1`, then it produces the normalized interface and forces
  the canonical cost unit.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaRealCalibration

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace PhysicalOneActCalibration

open DeltaRealCalibration

/-- A physical one-act instrument: a positive candidate unit, a real readout, a
proof that the readout is exactly the one-act curvature of that unit, and a lock
showing the readout equals one. -/
structure OneActInstrument where
  unit : ℝ
  positive : 0 < unit
  readout : ℝ
  reads_curvature : readout = oneActCurvature unit
  locked_to_one : readout = 1

/-- A one-act instrument supplies the normalized continuum-side interface. -/
def OneActInstrument.toInterface (I : OneActInstrument) : NormalizedOneActInterface where
  unit := I.unit
  positive := I.positive
  curvature_unit := by
    rw [← I.reads_curvature, I.locked_to_one]

/-- The physical one-act instrument forces the canonical cost unit. -/
theorem instrument_forces_canonical_unit (I : OneActInstrument) :
    I.unit = 1 :=
  normalized_interface_forces_J I.toInterface

/-- The canonical instrument exists at the canonical unit. This is a consistency
witness, not a construction of lab hardware. -/
def canonicalInstrument : OneActInstrument where
  unit := 1
  positive := by norm_num
  readout := 1
  reads_curvature := by
    rw [oneActCurvature_eq]
    norm_num
  locked_to_one := rfl

/-- **Physical calibration headline.** The abstract one-act normalization is
exactly the datum supplied by a physical one-act instrument: any such instrument
produces the normalized interface and forces `unit = 1`, and the canonical unit
carries a consistent instrument witness. -/
theorem physical_one_act_calibration_headline :
    (∀ I : OneActInstrument, I.unit = 1)
      ∧ (∃ I : OneActInstrument, I.unit = 1)
      ∧ (∀ I : OneActInstrument, (OneActInstrument.toInterface I).unit = I.unit) :=
  ⟨instrument_forces_canonical_unit, ⟨canonicalInstrument, rfl⟩, fun _ => rfl⟩

end PhysicalOneActCalibration
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

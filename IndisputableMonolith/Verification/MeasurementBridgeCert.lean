import Mathlib
import IndisputableMonolith.Measurement.C2ABridge

/-!
# Measurement Bridge Certificate (C = 2A and weight bridges)

This certificate packages the key **two-branch** measurement bridge theorems proved in
`IndisputableMonolith/Measurement/C2ABridge.lean`:

- `C = 2A` for the canonical path extracted from a two-branch rotation, and
- the corresponding weight identities (pathWeight = exp(-2A), hence Born weight).

It intentionally does **not** import any Quantum scaffolds or any “measurement axioms” typeclass.
-/

namespace IndisputableMonolith
namespace Verification
namespace MeasurementBridge

open IndisputableMonolith.Measurement

structure MeasurementBridgeCert where
  deriving Repr

@[simp] def MeasurementBridgeCert.verified (_c : MeasurementBridgeCert) : Prop :=
  (∀ rot : TwoBranchRotation,
      Measurement.pathAction (Measurement.pathFromRotation rot) = 2 * Measurement.rateAction rot)
  ∧
  (∀ rot : TwoBranchRotation,
      Measurement.pathWeight (Measurement.pathFromRotation rot) = Real.exp (- 2 * Measurement.rateAction rot))

@[simp] theorem MeasurementBridgeCert.verified_any (c : MeasurementBridgeCert) :
    MeasurementBridgeCert.verified c := by
  refine And.intro ?hC ?hW
  · intro rot
    exact Measurement.measurement_bridge_C_eq_2A rot
  · intro rot
    exact Measurement.weight_bridge rot

end MeasurementBridge
end Verification
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.RecogSpec.Spec

/-!
# UniqueCalibration Certificate (absolute-layer calibration is explicit)

This certificate packages the lemma `IndisputableMonolith.RecogSpec.uniqueCalibration_any`:
for every ledger/bridge and every anchor pair, there is a *unique* RS-units pack
calibrated to those anchors (with the speed determined by `speedFromAnchors`).

This is an **audit** certificate: it makes the “absolute-layer calibration witness”
explicit and machine-checked, rather than relying on implicit choice.
-/

namespace IndisputableMonolith
namespace Verification
namespace UniqueCalibration

open IndisputableMonolith.RecogSpec

structure UniqueCalibrationCert where
  deriving Repr

@[simp] def UniqueCalibrationCert.verified (_c : UniqueCalibrationCert) : Prop :=
  ∀ (L : RecogSpec.Ledger) (B : RecogSpec.Bridge L) (A : RecogSpec.Anchors),
    RecogSpec.UniqueCalibration L B A

@[simp] theorem UniqueCalibrationCert.verified_any (c : UniqueCalibrationCert) :
    UniqueCalibrationCert.verified c := by
  intro L B A
  exact RecogSpec.uniqueCalibration_any L B A

end UniqueCalibration
end Verification
end IndisputableMonolith

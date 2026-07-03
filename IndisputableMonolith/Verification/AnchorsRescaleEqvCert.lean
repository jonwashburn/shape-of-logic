import Mathlib
import IndisputableMonolith.RecogSpec.Spec
import IndisputableMonolith.Verification.UnitsFromAnchorsRescaleCert

/-!
# Anchors-Rescaling Equivalence Certificate

This audit certificate records that rescaling anchors by a positive factor `s`
does not change their **units-equivalence class** (the quotient by the speed
equivalence `AnchorsEqv`).

Rather than reproving the ratio algebra directly, we derive the speed invariance
from the already-certified `UnitsFromAnchorsRescaleCert`: since `UnitsRescaled`
fixes `c`, and `unitsFromAnchors` sets `c := speedFromAnchors`, the induced speeds
must be equal.
-/

namespace IndisputableMonolith
namespace Verification
namespace AnchorsRescaleEqv

open IndisputableMonolith.RecogSpec
open IndisputableMonolith.Verification.UnitsFromAnchorsRescale

structure AnchorsRescaleEqvCert where
  deriving Repr

@[simp] def AnchorsRescaleEqvCert.verified (_c : AnchorsRescaleEqvCert) : Prop :=
  ∀ (A : RecogSpec.Anchors) (s : ℝ), 0 < s →
    Quot.mk RecogSpec.anchorsSetoid A = Quot.mk RecogSpec.anchorsSetoid (rescaleAnchors s A)

@[simp] theorem AnchorsRescaleEqvCert.verified_any (c : AnchorsRescaleEqvCert) :
    AnchorsRescaleEqvCert.verified c := by
  intro A s hs
  have hNonempty :=
    IndisputableMonolith.Verification.UnitsFromAnchorsRescale.UnitsFromAnchorsRescaleCert.verified_any {} A s hs
  rcases hNonempty with ⟨hUU'⟩
  have hC :
      (RecogSpec.unitsFromAnchors (rescaleAnchors s A)).c = (RecogSpec.unitsFromAnchors A).c :=
    hUU'.cfix
  have hspeed : RecogSpec.speedFromAnchors A = RecogSpec.speedFromAnchors (rescaleAnchors s A) := by
    have : RecogSpec.speedFromAnchors (rescaleAnchors s A) = RecogSpec.speedFromAnchors A := by
      simpa [RecogSpec.unitsFromAnchors] using hC
    exact this.symm
  apply Quot.sound
  simpa [RecogSpec.AnchorsEqv] using hspeed

end AnchorsRescaleEqv
end Verification
end IndisputableMonolith

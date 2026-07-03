import Mathlib
import IndisputableMonolith.RecogSpec.Bands

/-!
# Bands-Invariance Certificate (c-band checker is dimensionless)

This audit certificate packages the fact that the absolute-layer band check

`evalToBands_c U X : Prop := ∃ b ∈ X, Band.contains b U.c`

is invariant under anchor rescalings (`Verification.UnitsRescaled`), because such
rescalings keep the speed parameter `c` fixed (`cfix`).
-/

namespace IndisputableMonolith
namespace Verification
namespace BandsInvariant

open IndisputableMonolith.RecogSpec

structure BandsInvariantCert where
  deriving Repr

@[simp] def BandsInvariantCert.verified (_c : BandsInvariantCert) : Prop :=
  ∀ {U U' : IndisputableMonolith.Constants.RSUnits}
    (_h : Verification.UnitsRescaled U U') (X : RecogSpec.Bands),
      RecogSpec.evalToBands_c U X ↔ RecogSpec.evalToBands_c U' X

@[simp] theorem BandsInvariantCert.verified_any (c : BandsInvariantCert) :
    BandsInvariantCert.verified c := by
  intro U U' h X
  exact RecogSpec.evalToBands_c_invariant (U := U) (U' := U') h X

end BandsInvariant
end Verification
end IndisputableMonolith

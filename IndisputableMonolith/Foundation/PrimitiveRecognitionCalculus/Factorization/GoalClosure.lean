/-
  PrimitiveRecognitionCalculus/Factorization/GoalClosure.lean

  D4 closure ledger for the factorization plan. The transform now exists in two
  theorem-level forms: classical transport of `Nat.primeFactorsList`, and a
  native noncomputable δ-choice transform by prime/factorization descent.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Factorization.PrimeCoordinateTransform

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace Factorization

open DistinctionNat

/-- The residual names allowed at the D4 finish line. -/
inductive PrimeCoordinateResidualName : Type
  | primeCoordinateReadout
  | characterSpectrumReadout
  | physicalPeriodReadout
  | classicalFactorizationTransport
deriving DecidableEq, Repr

/-- Current residual label retained for historical compatibility. The
commitment it names is closed below by the native-choice transform. -/
def currentPrimeCoordinateResidual : PrimeCoordinateResidualName :=
  .primeCoordinateReadout

/-- The original D4 commitment. Supplying this is exactly supplying the
δ-prime-coordinate transform, not a weaker benchmark or heuristic. It is now
closed by `deltaPrimeCoordinateTransform_classicalTransport`. -/
def PrimeCoordinateReadoutCommitment : Prop :=
  Nonempty DeltaPrimeCoordinateTransform

/-- Provenance of the currently closed transform. -/
inductive PrimeCoordinateTransformProvenance : Type
  | classicalFactorizationTransport
  | nativeDeltaReadout
deriving DecidableEq, Repr

/-- Current transform provenance: native δ choice by prime/factorization
descent. -/
def currentPrimeCoordinateTransformProvenance :
    PrimeCoordinateTransformProvenance :=
  .nativeDeltaReadout

theorem current_residual_named :
    currentPrimeCoordinateResidual = .primeCoordinateReadout := rfl

theorem primeCoordinateReadoutCommitment_exact :
    PrimeCoordinateReadoutCommitment ↔ Nonempty DeltaPrimeCoordinateTransform := by
  rfl

/-- The commitment is closed in the theorem-ledger sense by the native-choice
transform. -/
theorem primeCoordinateReadoutCommitment_closed :
    PrimeCoordinateReadoutCommitment :=
  deltaPrimeCoordinateTransform_nativeChoice_exists

theorem current_transform_provenance :
    currentPrimeCoordinateTransformProvenance =
      .nativeDeltaReadout := rfl

/-- If the named residual commitment is supplied, factor recovery is immediate.
This is the theorem-level content of "solving becomes coordinate readout." -/
theorem primeCoordinateReadoutCommitment_recovers_prime_divisor
    (h : PrimeCoordinateReadoutCommitment) :
    ∀ N : DistinctionNat, N ≠ zero → ¬ unit N →
      ∃ p : DistinctionNat, primeOrbit p ∧ divides p N := by
  rcases h with ⟨T⟩
  exact deltaPrimeCoordinateTransform_recovers_prime_divisor T

/-- D4 closure certificate. It records that factor recovery is closed by a
native noncomputable δ-choice transform; classical transport remains a separate
proved path in `PrimeCoordinateTransformCertificate`. -/
structure GoalClosureCertificate : Prop where
  residual_named :
    currentPrimeCoordinateResidual = .primeCoordinateReadout
  transform_provenance :
    currentPrimeCoordinateTransformProvenance =
      .nativeDeltaReadout
  residual_exact :
    PrimeCoordinateReadoutCommitment ↔ Nonempty DeltaPrimeCoordinateTransform
  residual_closed :
    PrimeCoordinateReadoutCommitment
  residual_would_recover :
    PrimeCoordinateReadoutCommitment →
      ∀ N : DistinctionNat, N ≠ zero → ¬ unit N →
        ∃ p : DistinctionNat, primeOrbit p ∧ divides p N

theorem goal_closure_certificate : GoalClosureCertificate where
  residual_named := current_residual_named
  transform_provenance := current_transform_provenance
  residual_exact := primeCoordinateReadoutCommitment_exact
  residual_closed := primeCoordinateReadoutCommitment_closed
  residual_would_recover := primeCoordinateReadoutCommitment_recovers_prime_divisor

end Factorization
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FiniteCertificateTransfer
import IndisputableMonolith.Economics.Recognition.Core

/-!
# Economic Observables

An economic observable is legitimate when display comparison agrees with the
native observable protocol. Continuum/display predicates are accepted only when
they are certificate-covered by a conservative completion.
-/

namespace IndisputableMonolith
namespace Economics
namespace Recognition

/-- A valid economic observable bridge: display comparisons are exactly native
observable comparisons. -/
def ValidEconObservable {N D O : Type*}
    (B : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison.Bridge N D O) :
    Prop :=
  ∀ x y : N,
    IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison.IsValidComparison B x y
      ↔ B.observeNative x = B.observeNative y

theorem validEconObservable_of_bridge {N D O : Type*}
    (B : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison.Bridge N D O) :
    ValidEconObservable B :=
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison.validComparison_iff_native B

/-- Conservative economic measurement: every display witness has a native
certificate. -/
def CertifiedEconPredicate {N D Cert : Type*}
    (C : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion N D Cert)
    (P : D → Prop) : Prop :=
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.ConservativeFor C P

theorem certified_iff_no_display_artifact {N D Cert : Type*}
    (C : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion N D Cert)
    (P : D → Prop) :
    CertifiedEconPredicate C P
      ↔ ¬ IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.ArtifactFor C P :=
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.conservative_iff_no_artifact C P

/-- Conservative display predicates transfer to finite/native certificates. -/
theorem certified_predicate_transfers {N D Cert : Type*}
    (C : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion N D Cert)
    (P : D → Prop)
    (h : CertifiedEconPredicate C P) :
    ∀ d : D, P d → ∃ c : Cert, C.certifies c d :=
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FiniteCertificateTransfer.conservative_completion_transfers C P h

/-- A concrete measurement datum: a display value together with the predicate
that says what it is supposed to measure. -/
structure EconMeasurement (D : Type*) where
  displayValue : D
  predicate : D → Prop

/-- A measurement is real exactly when its displayed witness has a native
certificate. -/
def MeasurementReal {N D Cert : Type*}
    (C : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion N D Cert)
    (m : EconMeasurement D) : Prop :=
  m.predicate m.displayValue ∧ ∃ cert : Cert, C.certifies cert m.displayValue

/-- A native certificate for a displayed economic measurement. -/
def CertifiesNative {N D Cert : Type*}
    (C : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion N D Cert)
    (cert : Cert) (m : EconMeasurement D) : Prop :=
  m.predicate m.displayValue ∧ C.certifies cert m.displayValue

/-- Measurement reality is equivalent to carrying a finite/native certificate for
the displayed witness. -/
theorem measurement_real_iff_certified {N D Cert : Type*}
    (C : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion N D Cert)
    (m : EconMeasurement D) :
    MeasurementReal C m ↔ ∃ cert : Cert, CertifiesNative C cert m := by
  unfold MeasurementReal CertifiesNative
  constructor
  · intro h
    rcases h with ⟨hP, cert, hcert⟩
    exact ⟨cert, hP, hcert⟩
  · intro h
    rcases h with ⟨cert, hP, hcert⟩
    exact ⟨hP, cert, hcert⟩

/-- If a predicate is certified and a measurement satisfies it, then the
measurement is real. -/
theorem measurement_real_of_certified_predicate {N D Cert : Type*}
    (C : IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion N D Cert)
    (m : EconMeasurement D)
    (hcertified : CertifiedEconPredicate C m.predicate)
    (hwitness : m.predicate m.displayValue) :
    MeasurementReal C m := by
  unfold MeasurementReal
  exact ⟨hwitness, hcertified m.displayValue hwitness⟩

/-! ## Concrete pass/fail measurement examples

These examples close the first finite-econometrics scaffold: one displayed
economic measurement passes because it is its own native certificate under the
identity completion; one displayed measurement fails because the completion has
no certificates at all.
-/

/-- Identity economic completion on natural-number displays. -/
def natIdentityEconCompletion :
    IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion ℕ ℕ ℕ :=
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.identityCompletion ℕ

/-- A concrete certified measurement: the displayed finite count is exactly 3. -/
def certifiedCountMeasurement : EconMeasurement ℕ where
  displayValue := 3
  predicate := fun d => d = 3

theorem certifiedCountMeasurement_real :
    MeasurementReal natIdentityEconCompletion certifiedCountMeasurement := by
  unfold MeasurementReal certifiedCountMeasurement natIdentityEconCompletion
  exact ⟨rfl, 3, rfl⟩

theorem certifiedCountMeasurement_has_native_certificate :
    ∃ cert : ℕ, CertifiesNative natIdentityEconCompletion cert certifiedCountMeasurement := by
  rw [← measurement_real_iff_certified]
  exact certifiedCountMeasurement_real

/-- A display completion that carries no native certificates. -/
def uncertifiedNatDisplayCompletion :
    IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.Completion Unit ℕ PEmpty where
  display := fun _ => 0
  certifies := fun _ _ => False

/-- A displayed claim with a true predicate but no possible certificate. -/
def uncertifiedDisplayMeasurement : EconMeasurement ℕ where
  displayValue := 1
  predicate := fun d => d = 1

theorem uncertifiedDisplayMeasurement_not_real :
    ¬ MeasurementReal uncertifiedNatDisplayCompletion uncertifiedDisplayMeasurement := by
  unfold MeasurementReal uncertifiedNatDisplayCompletion uncertifiedDisplayMeasurement
  intro h
  rcases h with ⟨_, cert, hcert⟩
  exact hcert

theorem uncertifiedDisplayMeasurement_artifact :
    IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.ArtifactFor
      uncertifiedNatDisplayCompletion uncertifiedDisplayMeasurement.predicate := by
  unfold IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity.ArtifactFor
  refine ⟨1, rfl, ?_⟩
  intro h
  rcases h with ⟨cert, hcert⟩
  exact hcert

/-! ## Source-manifested empirical artifacts

The Python `measurement_gate` accepts empirical JSON artifacts only when they
carry two finite witnesses: a nonempty payload and a nonempty source manifest.
The Lean layer below records that gate as a small theorem-backed interface.
-/

/-- Finite empirical payload witness. `witnessCount` is the number of finite
rows/nodes/cases/windows supplied by the artifact. -/
structure FiniteEmpiricalPayload where
  witnessCount : ℕ

/-- Source-manifest witness. `sourceCount` is the number of source records
attached to the artifact. -/
structure EmpiricalSourceManifest where
  sourceCount : ℕ

/-- A source-manifested empirical measurement artifact. -/
structure EmpiricalMeasurementArtifact where
  payload : FiniteEmpiricalPayload
  manifest : EmpiricalSourceManifest

/-- The artifact has a finite payload. -/
def FinitePayloadPresent (payload : FiniteEmpiricalPayload) : Prop :=
  0 < payload.witnessCount

/-- The artifact has a nonempty source manifest. -/
def SourceManifestComplete (manifest : EmpiricalSourceManifest) : Prop :=
  0 < manifest.sourceCount

/-- The WP6 empirical gate: finite payload plus source manifest. -/
def EmpiricalArtifactAdmissible (artifact : EmpiricalMeasurementArtifact) : Prop :=
  FinitePayloadPresent artifact.payload ∧ SourceManifestComplete artifact.manifest

theorem empiricalArtifact_admissible_iff
    (artifact : EmpiricalMeasurementArtifact) :
    EmpiricalArtifactAdmissible artifact ↔
      0 < artifact.payload.witnessCount ∧ 0 < artifact.manifest.sourceCount := by
  rfl

/-- Concrete admissible artifact, matching the source-manifested JSON reports. -/
def exampleAdmissibleArtifact : EmpiricalMeasurementArtifact where
  payload := { witnessCount := 3 }
  manifest := { sourceCount := 2 }

theorem exampleAdmissibleArtifact_certified :
    EmpiricalArtifactAdmissible exampleAdmissibleArtifact := by
  unfold EmpiricalArtifactAdmissible FinitePayloadPresent SourceManifestComplete exampleAdmissibleArtifact
  exact ⟨by norm_num, by norm_num⟩

/-- Concrete rejected artifact: it has a payload but no sources. -/
def exampleUnsourcedArtifact : EmpiricalMeasurementArtifact where
  payload := { witnessCount := 3 }
  manifest := { sourceCount := 0 }

theorem exampleUnsourcedArtifact_rejected :
    ¬ EmpiricalArtifactAdmissible exampleUnsourcedArtifact := by
  unfold EmpiricalArtifactAdmissible FinitePayloadPresent SourceManifestComplete exampleUnsourcedArtifact
  intro h
  exact Nat.not_lt_zero 0 h.2

end Recognition
end Economics
end IndisputableMonolith

/-
  PrimitiveRecognitionCalculus/DeltaNativeStrongClosure.lean

  Strong closure certificate for the Delta-native analysis program.

  The previous modules close the individual layers: protocol reals, finite
  generation, certified analytic registries, F_RS and F_RS[i], calibration,
  prime-axis coherence, cubical geometry, quotient selection, objecthood,
  finite probability, finite amplitude, valid comparison, completion
  conservativity, finite-certificate transfer, and hard-problem audit schemas.

  This module is the capstone. It does not add a new axiom or a new theorem
  family. It packages the existing theorem heads into one citeable certificate
  so the plan has a single Lean artifact meaning:

    "The Delta-native interface is closed at the theorem-schema and audit-schema
     level; further work is problem-specific theorem content inside typed
     interfaces."

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaReal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.GenerableReal
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CertifiedAnalyticProtocols
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CertifiedAnalyticTransformers
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FRSCarrier
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaRealCalibration
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PrimeAxisCoherence
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.MultiDistinctionGeometry
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientSelection
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuotientExamples
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ObjecthoodRegistry
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaProbability
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.DeltaAmplitude
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FRSComplexAmplitude
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.HilbertDisplayCompletion
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PhysicalOneActCalibration
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparison
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.ValidComparisonExamples
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CompletionConservativity
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FiniteCertificateTransfer
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.QuantizedProofMethod
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.HardProblemCertificateAudits
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CubicalChainComplex
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.AllDimensionalCubicalBoundary

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DeltaNativeStrongClosure

open CompletionConservativity

/-- A named proof entry in the strong closure certificate. -/
structure ClosureEntry where
  closed : Prop
  proof : closed

def entryOf (p : Prop) (h : p) : ClosureEntry := ⟨p, h⟩

/-- The full Delta-native strong closure certificate. Each field points to an
existing theorem head. Parameterized layers are stored as functions returning
closure entries. -/
structure StrongClosureCertificate where
  deltaReal : ClosureEntry
  generableCarrier : (ℕ → ℝ) → ClosureEntry
  certifiedAnalytic : CertifiedAnalyticProtocols.Registry → ClosureEntry
  certifiedTransformers : CertifiedAnalyticTransformers.RichRegistry → ClosureEntry
  frsCarrier : ClosureEntry
  calibration : ClosureEntry
  physicalCalibration : ClosureEntry
  primeAxis : ClosureEntry
  multiDistinctionGeometry : ClosureEntry
  cubicalTwoFace : ClosureEntry
  allDimensionalCubical : ClosureEntry
  quotientSelection : {X C : Type*} → Set (X → C) → ClosureEntry
  quotientEmptyExample : ClosureEntry
  quotientSeparatingExample : ClosureEntry
  quotientProjectiveExample : {State Obs : Type*} → Set (State → Obs) → State → State → ClosureEntry
  objecthoodTable : ClosureEntry
  backgroundObjectAudit : ClosureEntry
  displayObjectExtension : ClosureEntry
  finiteProbability : ℕ → ClosureEntry
  finiteAmplitude : ℕ → ClosureEntry
  complexAmplitude : ℕ → ClosureEntry
  frsiAmplitude : ℕ → ClosureEntry
  hilbertDisplay : ℕ → ClosureEntry
  physicalComparison :
    {N D E O : Type*} → ValidComparison.Bridge N D O → ValidComparison.Bridge D E O → ClosureEntry
  comparisonExamples : ClosureEntry
  completionConservativity : (N D Cert : Type*) → Completion N D Cert → ClosureEntry
  productCompletion :
    {N₁ D₁ Cert₁ N₂ D₂ Cert₂ : Type*} →
      Completion N₁ D₁ Cert₁ → Completion N₂ D₂ Cert₂ → (D₁ → Prop) → (D₂ → Prop) →
        ClosureEntry
  functionCompletion :
    Type* → {N D Cert : Type*} → Completion N D Cert → (D → Prop) → ClosureEntry
  finiteCertificateTransfer :
    {N D Cert : Type*} → (C : Completion N D Cert) → (P Obstruction : D → Prop) →
      ConservativeFor C P → ConservativeFor C Obstruction → ClosureEntry
  problemAuditReduction :
    {N D Cert : Type*} → QuantizedProofMethod.ProblemAudit N D Cert → ClosureEntry
  stubObligationReflexive : QuantizedProofMethod.ApplicationStub → ClosureEntry
  hardProblemAudits : ClosureEntry
  certifiedDisplayAudits : ClosureEntry
  domainSpecificAnalyticAudits : ClosureEntry

/-- The concrete certificate assembling the closed Delta-native theorem surface. -/
noncomputable def strongClosureCertificate : StrongClosureCertificate where
  deltaReal := entryOf _ DeltaReal.Protocol.display_real_forgetful
  generableCarrier := fun κ => entryOf _ (GenerableReal.genField_is_operational_carrier κ)
  certifiedAnalytic := fun R =>
    entryOf _ (CertifiedAnalyticProtocols.Expr.transcendental_protocol_closure R)
  certifiedTransformers := fun R =>
    entryOf _ (CertifiedAnalyticTransformers.certified_transformer_headline R)
  frsCarrier := entryOf _ FRSCarrier.frs_carrier
  calibration := entryOf _ DeltaRealCalibration.calibration_gap_closed_by_normalized_interface
  physicalCalibration := entryOf _ PhysicalOneActCalibration.physical_one_act_calibration_headline
  primeAxis := entryOf _ PrimeAxisCoherence.prime_axis_coherence
  multiDistinctionGeometry := entryOf _ MultiDistinctionGeometry.multi_distinction_geometry
  cubicalTwoFace := entryOf _ CubicalChainComplex.finite_two_face_ledger_square_zero
  allDimensionalCubical := entryOf _ AllDimensionalCubicalBoundary.all_dimensional_cubical_boundary_headline
  quotientSelection := fun F => entryOf _ (QuotientSelection.gauge_from_indistinguishability F)
  quotientEmptyExample := entryOf _ QuotientExamples.empty_observable_phase_quotient
  quotientSeparatingExample := entryOf _ QuotientExamples.separating_gauge_family_injective
  quotientProjectiveExample := fun F x y => entryOf _ (QuotientExamples.projective_state_display F x y)
  objecthoodTable := entryOf _ ObjecthoodRegistry.objecthood_periodic_table
  backgroundObjectAudit := entryOf _ ObjecthoodRegistry.background_object_audit
  displayObjectExtension := entryOf _ ObjecthoodRegistry.display_object_extension
  finiteProbability := fun N => entryOf _ (DeltaProbability.delta_probability_headline N)
  finiteAmplitude := fun N => entryOf _ (DeltaAmplitude.delta_amplitude_headline N)
  complexAmplitude := fun N => entryOf _ (DeltaAmplitude.delta_complex_amplitude_headline N)
  frsiAmplitude := fun N => entryOf _ (FRSComplexAmplitude.frsi_amplitude_headline N)
  hilbertDisplay := fun N => entryOf _ (HilbertDisplayCompletion.finite_hilbert_display_headline N)
  physicalComparison := fun B₁ B₂ => entryOf _ (ValidComparison.valid_comparison_doctrine B₁ B₂)
  comparisonExamples := entryOf _ ValidComparisonExamples.valid_comparison_examples_headline
  completionConservativity := fun N D Cert C =>
    entryOf _ (CompletionConservativity.completion_conservativity_headline N D Cert C)
  productCompletion := fun C₁ C₂ P₁ P₂ =>
    entryOf _ (CompletionConservativity.product_completion_headline C₁ C₂ P₁ P₂)
  functionCompletion := fun I {N} {D} {Cert} (C : Completion N D Cert) (P : D → Prop) =>
    entryOf _ (CompletionConservativity.function_completion_headline (I := I) C P)
  finiteCertificateTransfer := fun C P Obstruction hP hO =>
    entryOf _ (FiniteCertificateTransfer.finite_certificate_transfer C P Obstruction hP hO)
  problemAuditReduction := fun A => entryOf _ (QuantizedProofMethod.problemAudit_finiteReduction A)
  stubObligationReflexive := fun s => entryOf _ (show
    QuantizedProofMethod.StubObligation s = QuantizedProofMethod.StubObligation s from rfl)
  hardProblemAudits := entryOf _ HardProblemCertificateAudits.hard_problem_certificate_audits_headline
  certifiedDisplayAudits := entryOf _ HardProblemCertificateAudits.certified_display_audits_headline
  domainSpecificAnalyticAudits := entryOf _ HardProblemCertificateAudits.domain_specific_analytic_audits_headline

/-- **Delta-native strong closure.** The full Delta-native interface has a single
Lean certificate bundling every closed theorem/audit layer. -/
theorem delta_native_strong_closure : Nonempty StrongClosureCertificate :=
  ⟨strongClosureCertificate⟩

end DeltaNativeStrongClosure
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

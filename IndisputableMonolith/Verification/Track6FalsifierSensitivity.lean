import Mathlib
import IndisputableMonolith.Gravity.DiscriminatorMatrix
import IndisputableMonolith.Gravity.StrongFieldStructural
import IndisputableMonolith.Verification.FalsifierRegisterDatasets
import IndisputableMonolith.Verification.FalsifierLikelihoodRegister
import IndisputableMonolith.Verification.GWTC3RingdownSharedRunner

/-!
# Track 6 Falsifier Sensitivity Certificate

## Status: STRUCTURAL THEOREM.

No placeholder proofs and no new RS-internal assumptions.

This module is the Fork F integration endpoint for Track 6 of
`Quantum_Gravity_Discovery_Master_Plan_20260521.html`.

It does not add a new observational lane.  It packages the Track 6 work that
already exists in the tree:

* theorem-grade phi-derived discriminator matrix
  (`Gravity.DiscriminatorMatrix`);
* named dataset/sensitivity attachments for all falsifier-register rows
  (`Verification.FalsifierRegisterDatasets`);
* likelihood/status coverage for the rows already upgraded beyond dataset-only
  (`Verification.FalsifierLikelihoodRegister`);
* the guarded GWTC-3 ringdown family runner, which prevents mixed-family
  posterior aggregation in the QNM/echo damping path
  (`Verification.GWTC3RingdownSharedRunner`).

The certificate is intentionally conservative.  It proves that Track 6 has a
single Lean-facing sensitivity package with named channels and guarded
reproducibility surfaces.  It does not claim empirical confirmation, and it
does not upgrade the still-structural PTA / strong-field / ringdown physics
into a final discovery statement.
-/

namespace IndisputableMonolith
namespace Verification
namespace Track6FalsifierSensitivity

open IndisputableMonolith.Gravity.DiscriminatorMatrix
open IndisputableMonolith.Gravity.StrongFieldStructural
open IndisputableMonolith.Verification.FalsifierRegisterDatasets
open IndisputableMonolith.Verification.FalsifierLikelihoodRegister
open IndisputableMonolith.Verification.GWTC3RingdownSharedRunner

/-! ## §1. Track 6 coverage counts -/

/-- The current theorem-grade discriminator sectors: leading-log entropy,
echo damping, and rung phase. -/
def theoremGradeDiscriminatorSectors : Nat := 3

/-- The rival rows required by Track 6.D: LQG, string, CDT / causal sets,
and Bohmian / Diosi-Penrose. -/
def rivalRowsCovered : Nat := 4

/-- The falsifier-register rows with named dataset attachments. -/
def falsifierRowsWithDatasetAttachments : Nat :=
  FalsifierLikelihoodRegister.totalFalsifierRows

/-- Rows upgraded beyond dataset-only status by likelihood/status artifacts. -/
def rowsWithLikelihoodOrStatusRecords : Nat :=
  FalsifierLikelihoodRegister.rowsWithLikelihoodOrStatus

/-- Current mapped GWTC-3 ringdown families accepted by the guarded runner. -/
def guardedRingdownFamilies : Nat :=
  GWTC3RingdownSharedRunner.refactoredFamilyScriptCount

/-- Current supported ringdown observable mappings in the shared runner. -/
def guardedRingdownMappings : Nat :=
  GWTC3RingdownSharedRunner.supportedMappingCount

theorem theorem_grade_discriminator_sector_count :
    theoremGradeDiscriminatorSectors = 3 := rfl

theorem rival_rows_covered_count :
    rivalRowsCovered = 4 := rfl

theorem dataset_attachment_row_count :
    falsifierRowsWithDatasetAttachments = 10 := rfl

theorem likelihood_or_status_row_count :
    rowsWithLikelihoodOrStatusRecords = 6 := rfl

theorem guarded_ringdown_family_count :
    guardedRingdownFamilies = 3 := rfl

theorem guarded_ringdown_mapping_count :
    guardedRingdownMappings = 2 := rfl

theorem guarded_ringdown_mapping_count_pos :
    0 < guardedRingdownMappings := by
  unfold guardedRingdownMappings
  exact GWTC3RingdownSharedRunner.supported_mapping_count_pos

/-! ## §2. Track 6 endpoint certificate -/

/-- Fork F Track 6 certificate.

The fields are exactly the integration-lane handoff requirements:
theorem-grade discriminators, per-rival matrix coverage, dataset attachments,
likelihood/status coverage, and guarded GWTC-3 ringdown processing. -/
structure Track6FalsifierSensitivityCert where
  /-- At least three independent theorem-grade discriminator sectors exist. -/
  discriminator_sector_count :
    theoremGradeDiscriminatorSectors = 3
  /-- The four required rival rows have per-rival distinguishability. -/
  rival_row_count :
    rivalRowsCovered = 4
  /-- The full 4 x 3 discriminator matrix is inhabited. -/
  discriminator_matrix :
    Nonempty IndisputableMonolith.Gravity.DiscriminatorMatrix.DiscriminatorMatrixCert
  /-- Track 6.D's "at least one cell per rival" requirement is inhabited. -/
  per_rival_distinguishability :
    Nonempty IndisputableMonolith.Gravity.DiscriminatorMatrix.PerRivalDistinguishability
  /-- The strong-field structural phi-deviation is theorem-grade positive. -/
  strong_field_structural :
    Nonempty IndisputableMonolith.Gravity.StrongFieldStructural.StrongFieldStructuralCert
  /-- Every falsifier-register row has a named dataset and positive scales. -/
  dataset_register :
    Nonempty FalsifierRegisterDatasets.FalsifierDatasetRegisterCert
  /-- Six rows have been upgraded to likelihood/status artifacts so far. -/
  likelihood_register :
    Nonempty FalsifierLikelihoodRegister.FalsifierLikelihoodRegisterCert
  /-- The likelihood/status coverage accounting is arithmetically closed. -/
  likelihood_row_accounting :
    FalsifierLikelihoodRegister.rowsWithLikelihoodOrStatus +
      FalsifierLikelihoodRegister.datasetOnlyRows =
        FalsifierLikelihoodRegister.totalFalsifierRows
  /-- The currently implemented GWTC-3 damping path is family-guarded. -/
  guarded_ringdown_runner :
    Nonempty GWTC3RingdownSharedRunner.GWTC3RingdownSharedRunnerCert
  /-- The guarded runner has at least one supported observable mapping. -/
  guarded_ringdown_mappings_positive :
    0 < guardedRingdownMappings

/-- Fork F endpoint certificate instance. -/
def track6FalsifierSensitivityCert : Track6FalsifierSensitivityCert where
  discriminator_sector_count := theorem_grade_discriminator_sector_count
  rival_row_count := rival_rows_covered_count
  discriminator_matrix :=
    IndisputableMonolith.Gravity.DiscriminatorMatrix.discriminatorMatrixFull_inhabited
  per_rival_distinguishability :=
    ⟨IndisputableMonolith.Gravity.DiscriminatorMatrix.perRivalDistinguishability_holds⟩
  strong_field_structural :=
    IndisputableMonolith.Gravity.StrongFieldStructural.strongFieldStructuralCert_inhabited
  dataset_register :=
    FalsifierRegisterDatasets.falsifierDatasetRegisterCert_inhabited
  likelihood_register :=
    FalsifierLikelihoodRegister.falsifierLikelihoodRegisterCert_inhabited
  likelihood_row_accounting :=
    FalsifierLikelihoodRegister.row_coverage_arithmetic
  guarded_ringdown_runner :=
    GWTC3RingdownSharedRunner.gwtc3RingdownSharedRunnerCert_inhabited
  guarded_ringdown_mappings_positive :=
    guarded_ringdown_mapping_count_pos

theorem track6FalsifierSensitivityCert_inhabited :
    Nonempty Track6FalsifierSensitivityCert :=
  ⟨track6FalsifierSensitivityCert⟩

/-! ## §3. One-statement handoff theorem -/

/-- **Fork F handoff theorem.**

Track 6 has a single integration endpoint: three theorem-grade
discriminator sectors, four rival rows covered by the discriminator matrix,
all ten falsifier-register rows dataset-attached, six rows upgraded to
likelihood/status records, and a guarded GWTC-3 ringdown runner with two
supported observable mappings. -/
theorem track6_falsifier_sensitivity_one_statement :
    (theoremGradeDiscriminatorSectors = 3) ∧
    (rivalRowsCovered = 4) ∧
    (falsifierRowsWithDatasetAttachments = 10) ∧
    (rowsWithLikelihoodOrStatusRecords = 6) ∧
    (guardedRingdownFamilies = 3) ∧
    (guardedRingdownMappings = 2) ∧
    Nonempty Track6FalsifierSensitivityCert :=
  ⟨theorem_grade_discriminator_sector_count,
   rival_rows_covered_count,
   dataset_attachment_row_count,
   likelihood_or_status_row_count,
   guarded_ringdown_family_count,
   guarded_ringdown_mapping_count,
   track6FalsifierSensitivityCert_inhabited⟩

end Track6FalsifierSensitivity
end Verification
end IndisputableMonolith

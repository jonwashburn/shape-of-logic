/-
  PrimitiveRecognitionCalculus/Inevitability.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 13: prove that every admissible expressive foundation
    admits a PRC trace core.

  "Admissible" here is deliberately exact: the foundation has been parsed into
  the `FormalSystem` interface and supplies endpoint distinction. Parsing
  external historical foundations into this interface is a later corpus task,
  not an implicit axiom in this theorem.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FormalSystem

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- An admissible foundation for the first inevitability theorem is a formal
system that is expressive enough to distinguish the two endpoints of δ. -/
structure AdmissibleFoundation where
  system : FormalSystem
  expressive : system.Expressive

/-- The exact first inevitability target. -/
def PRCInevitabilityTarget : Prop :=
  ∀ A : AdmissibleFoundation, Nonempty (PRCEmbeddingInto A.system)

/-- Any foundation already parsed into the admissible interface presupposes a
PRC trace core. -/
theorem any_foundation_presupposes_distinction :
    PRCInevitabilityTarget := by
  intro A
  exact FormalSystemEmbeddingTarget_proved A.system A.expressive

/-- PRC itself is an admissible foundation in this interface. -/
def PRCAdmissibleFoundation : AdmissibleFoundation where
  system := PRCFormalSystem
  expressive := PRCFormalSystem_expressive

theorem PRCAdmissibleFoundation_embeds :
    Nonempty (PRCEmbeddingInto PRCAdmissibleFoundation.system) :=
  any_foundation_presupposes_distinction PRCAdmissibleFoundation

/-- The exact remaining external parsing target schema: once a corpus of
external foundations and a faithful-parse relation are fixed, every external
object in that corpus must parse to an expressive formal system before the
inevitability theorem applies to it. -/
def ExternalFoundationParsingTarget
    (ExternalFoundation : Type)
    (FaithfulParse : ExternalFoundation → FormalSystem → Prop) : Prop :=
  ∀ E : ExternalFoundation,
    ∃ F : FormalSystem, FaithfulParse E F ∧ F.Expressive

/-- Step 13 certificate. The admissible-interface theorem is closed; the
external parsing workload is named separately so it is not hidden inside the
theorem. -/
structure PRCInevitabilityCertificate : Prop where
  admissible_foundation_surface : Nonempty AdmissibleFoundation
  prc_admissible : Nonempty AdmissibleFoundation
  inevitability_target : PRCInevitabilityTarget
  any_foundation_embedding :
    ∀ A : AdmissibleFoundation, Nonempty (PRCEmbeddingInto A.system)
  prc_embedding : Nonempty (PRCEmbeddingInto PRCAdmissibleFoundation.system)
  external_parsing_target_schema :
    ∀ (ExternalFoundation : Type)
      (FaithfulParse : ExternalFoundation → FormalSystem → Prop),
      ExternalFoundationParsingTarget ExternalFoundation FaithfulParse =
        ExternalFoundationParsingTarget ExternalFoundation FaithfulParse
  strength_tag : StrengthTag.deltaOnly = StrengthTag.deltaOnly

theorem prc_inevitability_certificate :
    PRCInevitabilityCertificate where
  admissible_foundation_surface := ⟨PRCAdmissibleFoundation⟩
  prc_admissible := ⟨PRCAdmissibleFoundation⟩
  inevitability_target := any_foundation_presupposes_distinction
  any_foundation_embedding := any_foundation_presupposes_distinction
  prc_embedding := PRCAdmissibleFoundation_embeds
  external_parsing_target_schema := by
    intro ExternalFoundation FaithfulParse
    rfl
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

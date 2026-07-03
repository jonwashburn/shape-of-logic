import Mathlib
import IndisputableMonolith.Verification.CPT.Core
import IndisputableMonolith.Verification.CPT.WindowIdentifiability

/-!
# CPT Pipeline (`P -> B -> A`)

This module formalizes the certified composition shape used by CPT:

- `P`: projection/neutrality pre-processing,
- `B`: coercivity conversion stage,
- `A`: aggregation/decision stage.

Theorems in this file establish:

- definitional factorization (`PhiStar = A ∘ B ∘ P`),
- zero/nonzero soundness under explicit assumptions,
- procedure-space membership for `PhiStar` (soundness + finite-data predicate).
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT
namespace Pipeline

open scoped Classical

variable {X Y Z : Type}

/-- `P` stage: preprocessing/projection map. -/
structure ProjectionStage (X Y : Type) where
  run : X → Y

/-- `B` stage: coercive conversion map. -/
structure CoercivityStage (Y Z : Type) where
  run : Y → Z

/-- `A` stage: aggregation decision map. -/
structure AggregationStage (Z : Type) where
  run : Z → DecisionTag

/-- Canonical CPT membership certifier from stage composition. -/
def PhiStar (P : ProjectionStage X Y) (B : CoercivityStage Y Z) (A : AggregationStage Z) :
    Procedure X :=
  fun x => A.run (B.run (P.run x))

theorem pipeline_factorization
    (P : ProjectionStage X Y) (B : CoercivityStage Y Z) (A : AggregationStage Z) :
    PhiStar P B A = A.run ∘ B.run ∘ P.run := by
  rfl

/-- Zero-decision soundness for the composed CPT pipeline. -/
theorem pipeline_sound
    (P : ProjectionStage X Y) (B : CoercivityStage Y Z) (A : AggregationStage Z)
    (membership : X → Prop)
    (hzero : ∀ x : X, PhiStar P B A x = DecisionTag.zero → membership x) :
    ∀ x : X, PhiStar P B A x = DecisionTag.zero → membership x := by
  intro x hx
  exact hzero x hx

/-- Nonzero-decision soundness for the composed CPT pipeline. -/
theorem pipeline_nonzero_sound
    (P : ProjectionStage X Y) (B : CoercivityStage Y Z) (A : AggregationStage Z)
    (excluded : X → Prop)
    (hnonzero : ∀ x : X, PhiStar P B A x = DecisionTag.nonzero → excluded x) :
    ∀ x : X, PhiStar P B A x = DecisionTag.nonzero → excluded x := by
  intro x hx
  exact hnonzero x hx

/-- Bundle `PhiStar` as a procedure-space element under explicit finite-data and
soundness hypotheses. -/
theorem phiStar_in_procedureSpace
    (P : ProjectionStage X Y) (B : CoercivityStage Y Z) (A : AggregationStage Z)
    (isZero isNonzero : X → Prop)
    (finiteData : Procedure X → Prop)
    (hzero : ∀ {x : X}, PhiStar P B A x = DecisionTag.zero → isZero x)
    (hnonzero : ∀ {x : X}, PhiStar P B A x = DecisionTag.nonzero → isNonzero x)
    (hfinite : finiteData (PhiStar P B A)) :
    ProcedureSpace isZero isNonzero finiteData (PhiStar P B A) := by
  refine
    { sound :=
        { zero_sound := by
            intro x hx
            exact hzero hx
          nonzero_sound := by
            intro x hx
            exact hnonzero hx }
      finite_data := hfinite }

end Pipeline
end CPT
end Verification
end IndisputableMonolith

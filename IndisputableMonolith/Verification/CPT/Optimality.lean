import Mathlib
import IndisputableMonolith.Verification.CPT.Core
import IndisputableMonolith.Verification.CPT.Pipeline

/-!
# CPT Optimality (Domination on a Class)

This module formalizes a class-restricted domination relation for CPT procedures and
proves a clean domination theorem for `PhiStar` under explicit assumptions:

- `Psi` resolves every input in the target class,
- `PhiStar` and `Psi` agree on that class.

The theorem intentionally keeps hypotheses explicit, matching claim-hygiene requirements.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT
namespace Optimality

open scoped Classical

variable {X Y Z : Type}

abbrev PhiStar
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z) : Procedure X :=
  Pipeline.PhiStar P B A

/-- A procedure resolves every point in class `C` if it never returns `inconclusive` on `C`. -/
def ResolvesClass (C : Set X) (Φ : Procedure X) : Prop :=
  ∀ ⦃x : X⦄, x ∈ C → Φ x ≠ DecisionTag.inconclusive

theorem procedure_resolves_class
    (C : Set X) (Φ : Procedure X)
    (hResolve : ResolvesClass C Φ) :
    C ⊆ resolvedSet Φ := by
  intro x hxC
  exact hResolve hxC

theorem phiStar_in_procedureSpace
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (isZero isNonzero : X → Prop)
    (finiteData : Procedure X → Prop)
    (hzero : ∀ {x : X}, PhiStar P B A x = DecisionTag.zero → isZero x)
    (hnonzero : ∀ {x : X}, PhiStar P B A x = DecisionTag.nonzero → isNonzero x)
    (hfinite : finiteData (PhiStar P B A)) :
    ProcedureSpace isZero isNonzero finiteData (PhiStar P B A) :=
  Pipeline.phiStar_in_procedureSpace P B A isZero isNonzero finiteData hzero hnonzero hfinite

theorem phiStar_resolves_nondegenerate
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (C : Set X)
    (hResolve : ResolvesClass C (PhiStar P B A)) :
    C ⊆ resolvedSet (PhiStar P B A) :=
  procedure_resolves_class C (PhiStar P B A) hResolve

/-- Domination/optimality on a class:
if `Psi` resolves the class and agrees with `PhiStar` on that class, then `PhiStar`
dominates `Psi` on that class. -/
theorem phiStar_dominates
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (C : Set X)
    (Ψ : Procedure X)
    (hPsiResolve : ResolvesClass C Ψ)
    (hAgreeOnClass : ∀ ⦃x : X⦄, x ∈ C → PhiStar P B A x = Ψ x) :
    dominatesOn C (PhiStar P B A) Ψ := by
  constructor
  · intro x hx
    rcases hx with ⟨hxC, _hxResPsi⟩
    have hΨ_on_class : x ∈ resolvedSet Ψ :=
      (procedure_resolves_class C Ψ hPsiResolve) hxC
    have hEq : PhiStar P B A x = Ψ x := hAgreeOnClass hxC
    have hΦ_on_class : x ∈ resolvedSet (PhiStar P B A) := by
      simpa [resolvedSet, hEq] using hΨ_on_class
    exact ⟨hxC, hΦ_on_class⟩
  · intro x hx
    exact hAgreeOnClass hx.1

/-- Global-class specialization of domination (`C = Set.univ`). -/
theorem phiStar_dominates_global
    (P : Pipeline.ProjectionStage X Y)
    (B : Pipeline.CoercivityStage Y Z)
    (A : Pipeline.AggregationStage Z)
    (Ψ : Procedure X)
    (hPsiResolve : ResolvesClass (Set.univ : Set X) Ψ)
    (hAgreeGlobal : ∀ x : X, PhiStar P B A x = Ψ x) :
    dominatesOn (Set.univ : Set X) (PhiStar P B A) Ψ := by
  exact phiStar_dominates P B A (Set.univ : Set X) Ψ hPsiResolve (by
    intro x _hx
    exact hAgreeGlobal x)

end Optimality
end CPT
end Verification
end IndisputableMonolith

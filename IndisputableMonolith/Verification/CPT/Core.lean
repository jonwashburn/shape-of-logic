import Mathlib
import IndisputableMonolith.CPM.LawOfExistence

/-!
# CPT Verification Core

This module provides small reusable interfaces for the CPT formalization:

- decision tags (`zero/nonzero/inconclusive`),
- procedure and resolved-set utilities,
- class-restricted domination relation,
- lightweight wrappers around the CPM A/B/C closure theorems.

The intent is to keep theorem statements claim-honest and composable across:
`WindowIdentifiability`, `Pipeline`, `Optimality`, and `ForcedFactorization`.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPT

open scoped Classical

/-- Ternary decision output used by CPT-style procedures. -/
inductive DecisionTag
  | zero
  | nonzero
  | inconclusive
  deriving DecidableEq, Repr

/-- A CPT procedure on inputs of type `X`. -/
abbrev Procedure (X : Type) : Type := X → DecisionTag

/-- Inputs resolved by a procedure (i.e., not `inconclusive`). -/
def resolvedSet {X : Type} (Φ : Procedure X) : Set X :=
  {x | Φ x ≠ DecisionTag.inconclusive}

/-- Resolved inputs inside a class `C`. -/
def resolvedSetOn {X : Type} (C : Set X) (Φ : Procedure X) : Set X :=
  {x | x ∈ C ∧ x ∈ resolvedSet Φ}

/-- Domination on a restricted class: `Φ` resolves at least what `Ψ` resolves on `C`,
and agrees with `Ψ` wherever `Ψ` resolves on `C`. -/
def dominatesOn {X : Type} (C : Set X) (Φ Ψ : Procedure X) : Prop :=
  resolvedSetOn C Ψ ⊆ resolvedSetOn C Φ
  ∧
  ∀ ⦃x : X⦄, x ∈ resolvedSetOn C Ψ → Φ x = Ψ x

/-- Soundness specification for ternary procedures:
`zero` certifies `isZero`; `nonzero` certifies `isNonzero`. -/
structure SoundProcedure {X : Type}
    (isZero isNonzero : X → Prop) (Φ : Procedure X) : Prop where
  zero_sound : ∀ {x : X}, Φ x = DecisionTag.zero → isZero x
  nonzero_sound : ∀ {x : X}, Φ x = DecisionTag.nonzero → isNonzero x

/-- A procedure-space package used in optimality theorems:
soundness plus an abstract finite-data predicate. -/
structure ProcedureSpace {X : Type}
    (isZero isNonzero : X → Prop) (finiteData : Procedure X → Prop)
    (Φ : Procedure X) : Prop where
  sound : SoundProcedure isZero isNonzero Φ
  finite_data : finiteData Φ

namespace CPMBridge

open IndisputableMonolith.CPM.LawOfExistence

variable {β : Type}

/-- CPT `B`-stage wrapper for AB-forward coercivity. -/
theorem b_stage_forward_coercivity
    (M : Model β) (a : β) :
    M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Ceng) * M.energyGap a :=
  M.defect_le_constants_mul_energyGap a

/-- CPT `B`-stage wrapper for AB-reverse coercivity. -/
theorem b_stage_reverse_coercivity
    (M : Model β)
    (hpos : 0 < M.C.Knet ∧ 0 < M.C.Cproj ∧ 0 < M.C.Ceng)
    (a : β) :
    M.energyGap a ≥ cmin M.C * M.defectMass a :=
  M.energyGap_ge_cmin_mul_defect hpos a

/-- CPT `A`-stage wrapper for AC aggregation. -/
theorem a_stage_aggregation
    (M : Model β) (a : β) :
    M.defectMass a ≤ (M.C.Knet * M.C.Cproj * M.C.Cdisp) * M.tests a :=
  M.defect_le_constants_mul_tests a

end CPMBridge

end CPT
end Verification
end IndisputableMonolith

/-
  PrimitiveRecognitionCalculus/SameDiff.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K2.6-K2.10, R5-R7, K4.2-K4.3

  This module does not define object equality as Lean equality. It defines
  an admissible trace-judgment surface: SameT, DiffT, consistency, and the
  substitution rule for contexts that respect SameT.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Basic

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K2.6-K2.8. An admissible trace judgment surface. -/
structure TraceJudgment where
  /-- K2.7. Object-level equality at a trace. -/
  same : Trace → Endpoint → Endpoint → Prop
  /-- K2.6. Object-level witnessed difference at a trace. -/
  diff : Trace → Endpoint → Endpoint → Prop
  /-- R5. SameT must be reflexive at each trace. -/
  same_refl_proof : ∀ T : Trace, Reflexive (same T)
  /-- R5. SameT must be symmetric at each trace. -/
  same_symm_proof : ∀ T : Trace, Symmetric (same T)
  /-- R5. SameT must be transitive at each trace. -/
  same_trans_proof : ∀ T : Trace, Transitive (same T)
  /-- R6. SameT and DiffT cannot both hold for the same ordered pair. -/
  same_diff_exclusive :
    ∀ {T : Trace} {a b : Endpoint}, same T a b → diff T a b → False

namespace TraceJudgment

/-- Reflexivity of SameT, extracted from the admissibility field. -/
theorem same_refl (J : TraceJudgment) (T : Trace) (a : Endpoint) :
    J.same T a a :=
  J.same_refl_proof T a

/-- Symmetry of SameT, extracted from the admissibility field. -/
theorem same_symm (J : TraceJudgment) (T : Trace) {a b : Endpoint}
    (h : J.same T a b) :
    J.same T b a :=
  J.same_symm_proof T h

/-- Transitivity of SameT, extracted from the admissibility field. -/
theorem same_trans (J : TraceJudgment) (T : Trace) {a b c : Endpoint}
    (hab : J.same T a b) (hbc : J.same T b c) :
    J.same T a c :=
  J.same_trans_proof T hab hbc

end TraceJudgment

/-- K2.8. A trace is consistent for a judgment surface if it never asserts
SameT and DiffT for the same endpoints. -/
def Consistent (J : TraceJudgment) (T : Trace) : Prop :=
  ∀ a b : Endpoint, ¬ (J.same T a b ∧ J.diff T a b)

/-- R6. The exclusivity field gives consistency at every trace. -/
theorem consistent_of_exclusive (J : TraceJudgment) (T : Trace) :
    Consistent J T := by
  intro a b h
  exact J.same_diff_exclusive h.1 h.2

/-- A predicate respects SameT at a trace. -/
def RespectsSame (J : TraceJudgment) (T : Trace)
    (P : Endpoint → Prop) : Prop :=
  ∀ {a b : Endpoint}, J.same T a b → P a → P b

/-- K2.10 and R7. Substitution for contexts that respect SameT. -/
theorem substitute
    (J : TraceJudgment) (T : Trace) (P : Endpoint → Prop)
    (hP : RespectsSame J T P) {a b : Endpoint}
    (hsame : J.same T a b) (ha : P a) :
    P b :=
  hP hsame ha

/-- A verifier-level model of the SameT/DiffT interface.

This is not PRC's object-level primitive. It is a sanity model showing the
interface is inhabited in Lean's verifier language. -/
def verifierEqualityJudgment : TraceJudgment where
  same := fun _ a b => a = b
  diff := fun _ a b => a ≠ b
  same_refl_proof := by
    intro T a
    rfl
  same_symm_proof := by
    intro T a b h
    exact h.symm
  same_trans_proof := by
    intro T a b c hab hbc
    exact hab.trans hbc
  same_diff_exclusive := by
    intro T a b hsame hdiff
    exact hdiff hsame

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

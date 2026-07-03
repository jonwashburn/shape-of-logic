/-
  PrimitiveRecognitionCalculus/Quotient.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K2.11, K4.4

  Quotienting is permitted only after SameT is known to be an equivalence.
  This module builds endpoint trace-classes and the corresponding recursion
  principle for SameT-respecting maps.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.SameDiff

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K2.11. The setoid induced by SameT at a fixed trace. -/
def sameSetoid (J : TraceJudgment) (T : Trace) : Setoid Endpoint where
  r := J.same T
  iseqv := {
    refl := J.same_refl_proof T
    symm := by
      intro a b h
      exact J.same_symm_proof T h
    trans := by
      intro a b c hab hbc
      exact J.same_trans_proof T hab hbc
  }

/-- K2.11. Endpoint trace-classes under SameT. -/
def EndpointClass (J : TraceJudgment) (T : Trace) : Type :=
  Quot (sameSetoid J T)

/-- The class of an endpoint. -/
def endpointClassOf (J : TraceJudgment) (T : Trace)
    (a : Endpoint) : EndpointClass J T :=
  Quot.mk (sameSetoid J T) a

/-- K4.4. SameT endpoints determine the same quotient class. -/
theorem endpointClass_eq_of_same
    (J : TraceJudgment) (T : Trace) {a b : Endpoint}
    (h : J.same T a b) :
    endpointClassOf J T a = endpointClassOf J T b :=
  Quot.sound h

/-- K4.4. Quotient recursion for SameT-respecting maps. -/
def endpointClassLift
    (J : TraceJudgment) (T : Trace) {α : Sort _}
    (f : Endpoint → α)
    (hf : ∀ {a b : Endpoint}, J.same T a b → f a = f b) :
    EndpointClass J T → α :=
  Quot.lift f (by
    intro a b h
    exact hf h)

@[simp] theorem endpointClassLift_mk
    (J : TraceJudgment) (T : Trace) {α : Sort _}
    (f : Endpoint → α)
    (hf : ∀ {a b : Endpoint}, J.same T a b → f a = f b)
    (a : Endpoint) :
    endpointClassLift J T f hf (endpointClassOf J T a) = f a := by
  rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

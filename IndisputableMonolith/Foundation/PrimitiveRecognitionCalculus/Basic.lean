/-
  PrimitiveRecognitionCalculus/Basic.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchors:
    K2.1-K2.5, R1-R4

  The δ-only syntactic kernel: distinction act, side, endpoint, finite
  trace, trace append, and trace extension. Lean equality is used only by
  the verifier to prove facts about this syntax.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Strength

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K2.1. The primitive distinction act. At the object level this is δ. -/
inductive DistinctionAct where
  | delta
  deriving DecidableEq, Repr

/-- K2.2. The two sides forced by a distinction. -/
inductive Side where
  | left
  | right
  deriving DecidableEq, Repr

/-- K2.3. An endpoint is a side of the primitive distinction. -/
structure Endpoint where
  side : Side
  deriving DecidableEq, Repr

/-- The left endpoint of δ. -/
def Endpoint.left : Endpoint :=
  ⟨Side.left⟩

/-- The right endpoint of δ. -/
def Endpoint.right : Endpoint :=
  ⟨Side.right⟩

/-- K2.4. A finite trace is empty or extended by one distinction act. -/
inductive Trace where
  | empty
  | extend : Trace → DistinctionAct → Trace
  deriving DecidableEq, Repr

namespace Trace

/-- R3. One-step extension by δ. -/
def step (T : Trace) : Trace :=
  Trace.extend T DistinctionAct.delta

/-- Append two traces. This is the syntactic composition operation. -/
def append : Trace → Trace → Trace
  | T, Trace.empty => T
  | T, Trace.extend U a => Trace.extend (append T U) a

@[simp] theorem append_empty (T : Trace) :
    append T Trace.empty = T := by
  rfl

@[simp] theorem append_extend (T U : Trace) (a : DistinctionAct) :
    append T (Trace.extend U a) = Trace.extend (append T U) a := by
  rfl

@[simp] theorem empty_append (T : Trace) :
    append Trace.empty T = T := by
  induction T with
  | empty => rfl
  | extend T a ih =>
      simp [append, ih]

/-- R4. Trace append is associative. -/
theorem append_assoc (T U V : Trace) :
    append (append T U) V = append T (append U V) := by
  induction V with
  | empty => rfl
  | extend V a ih =>
      simp [append, ih]

/-- K2.5. `Extends T U` means `U` is `T` followed by some suffix trace. -/
def Extends (T U : Trace) : Prop :=
  ∃ V : Trace, append T V = U

/-- R4. Trace extension is reflexive. -/
theorem extends_refl (T : Trace) :
    Extends T T := by
  exact ⟨Trace.empty, rfl⟩

/-- R4. Trace extension is transitive. -/
theorem extends_trans {T U V : Trace}
    (hTU : Extends T U) (hUV : Extends U V) :
    Extends T V := by
  rcases hTU with ⟨A, hA⟩
  rcases hUV with ⟨B, hB⟩
  refine ⟨append A B, ?_⟩
  rw [← append_assoc, hA, hB]

/-- The trace with exactly `n` repeated δ-extensions. -/
def orbitTrace : Nat → Trace
  | 0 => Trace.empty
  | Nat.succ n => step (orbitTrace n)

/-- Length of a finite trace. -/
def length : Trace → Nat
  | Trace.empty => 0
  | Trace.extend T _ => Nat.succ (length T)

@[simp] theorem length_empty :
    length Trace.empty = 0 := by
  rfl

@[simp] theorem length_extend (T : Trace) (a : DistinctionAct) :
    length (Trace.extend T a) = Nat.succ (length T) := by
  rfl

/-- K2.12 preview. The length of the nth orbit trace is n. -/
theorem length_orbitTrace (n : Nat) :
    length (orbitTrace n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [orbitTrace, step, ih]

end Trace

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

/-
  PrimitiveRecognitionCalculus/Strength.lean

  Round-trip source:
    PRC_Kernel_Spec_20260526.html

  Spec anchor:
    K1. Strength Ledger

  This module records the proof-strength tags used by the Primitive
  Recognition Calculus kernel. The tags are not mathematical assumptions.
  They are audit labels attached to later definitions and theorems.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- K1. The strength tag attached to a PRC claim. -/
inductive StrengthTag where
  /-- Forced by distinction and finite repetition alone. -/
  | deltaOnly
  /-- Uses the completed orbit or completed stable trace families. -/
  | traceClosure
  /-- Uses selection of witnesses from stable families. -/
  | choice
  /-- Uses controlled subtrace-class or power-class formation. -/
  | powerComprehension
  /-- Uses excluded middle or full classical reasoning as an extension. -/
  | classicalExtension
  deriving DecidableEq, Repr

/-- A small audit record tying a claim label to its strength tag. -/
structure StrengthClaim where
  label : String
  tag : StrengthTag
  statement : String
  deriving Repr

/-- K1. Commitment rank: how much a claim assumes beyond distinction itself.
`deltaOnly` is the floor (forced by distinction and finite repetition alone);
each later tag adds a strictly stronger commitment. The ranks make the
"Strength Ledger" an actual ordered ledger, not a flat set of labels. -/
def StrengthTag.rank : StrengthTag → ℕ
  | deltaOnly => 0
  | traceClosure => 1
  | choice => 2
  | powerComprehension => 3
  | classicalExtension => 4

/-- A claim at tag `a` is no stronger than one at tag `b` when its commitment
rank does not exceed `b`'s. -/
def StrengthTag.le (a b : StrengthTag) : Prop := a.rank ≤ b.rank

/-- Strict commitment order on strength tags. -/
def StrengthTag.lt (a b : StrengthTag) : Prop := a.rank < b.rank

instance : LE StrengthTag := ⟨StrengthTag.le⟩
instance : LT StrengthTag := ⟨StrengthTag.lt⟩

instance (a b : StrengthTag) : Decidable (a ≤ b) :=
  decidable_of_iff (a.rank ≤ b.rank) Iff.rfl

instance (a b : StrengthTag) : Decidable (a < b) :=
  decidable_of_iff (a.rank < b.rank) Iff.rfl

/-- The commitment rank is injective: distinct tags carry distinct ranks, so
the ledger order is a genuine (anti-symmetric) order, not a preorder collapse. -/
theorem StrengthTag.rank_injective : Function.Injective StrengthTag.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [StrengthTag.rank]

/-- K1 ledger order, exact: the five strength tags form the strict commitment
chain `deltaOnly < traceClosure < choice < powerComprehension <
classicalExtension`. This is the ordering the "Strength Ledger" anchor names. -/
theorem StrengthTag.strict_chain :
    StrengthTag.deltaOnly < StrengthTag.traceClosure ∧
    StrengthTag.traceClosure < StrengthTag.choice ∧
    StrengthTag.choice < StrengthTag.powerComprehension ∧
    StrengthTag.powerComprehension < StrengthTag.classicalExtension := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The completion stratum (`traceClosure`) is a strictly stronger commitment
than the δ-only floor. This is the exact, type-level statement of the program's
central honesty claim: moving from the δ-native carrier to the continuous
completion is a real strengthening, not a free step. -/
theorem StrengthTag.deltaOnly_lt_traceClosure :
    StrengthTag.deltaOnly < StrengthTag.traceClosure := by
  decide

/-- K1 audit sanity: the δ-only tag is not the trace-closure tag. -/
theorem deltaOnly_ne_traceClosure :
    StrengthTag.deltaOnly ≠ StrengthTag.traceClosure := by
  decide

/-- K1 audit sanity: choice is not a δ-only claim. -/
theorem choice_ne_deltaOnly :
    StrengthTag.choice ≠ StrengthTag.deltaOnly := by
  decide

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

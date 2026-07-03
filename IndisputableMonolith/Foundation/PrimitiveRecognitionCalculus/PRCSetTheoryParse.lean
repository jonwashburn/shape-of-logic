/-
  PrimitiveRecognitionCalculus/PRCSetTheoryParse.lean

  Item 4 of the δ frontier, first real corpus parse: hereditarily finite set
  theory (ZFC minus the axiom of infinity), faithfully encoded, shown to contain δ.

  Prior δ4 work gave a toy set-theory witness: `ofTwoDistinct (∅ : Set Unit) univ`,
  which is really just a two-point Boolean. That does not parse set theory; it
  relabels a truth value. This module does the genuine thing.

  We use the Ackermann coding of the hereditarily finite sets: a natural number `n`
  codes the HF set whose members are exactly the codes `i` with bit `i` of `n` set,

      i ∈ n   ⟺   bit i of n is 1.

  This is the standard bijection between ℕ and the hereditarily finite sets, the
  canonical model of ZFC with infinity removed (equivalently, V_ω). On this coding:

  * EXTENSIONALITY holds (`ext_iff`): two codes are equal iff they have the same
    members. This is the axiom of extensionality, and it is exactly ℕ bit
    extensionality.
  * The EMPTY SET is coded by 0 (`not_mem_empty`): it has no members.
  * The SINGLETON {∅} is coded by 1 (`mem_one_iff`): its only member is 0 = ∅.
  * Hence ∅ ≠ {∅} as SETS, because they have different members, not merely
    different codes (`distinguishes_iff_extensional`).

  `hfSystem` parses this foundation into the `FormalSystem` interface: tokens are HF
  set codes, the discrimination relation is the foundation's own extensional set
  inequality, the endpoints are the genuine ∅ and {∅} (the von Neumann 0 and 1).
  It is `Expressive`, so it realizes the δ core, and it falls on the δ side of the
  distinction dichotomy.

  HONEST BOUNDARY (now lifted by `PRCFullZFCParse.lean`). This module is HF set
  theory (ZFC − infinity): every code is a finite set, so the axiom of infinity is
  not modelled here. The δ core needs only the extensional distinction, which HF
  already provides. Full ZFC WITH the axiom of infinity is handled in
  `PRCFullZFCParse.lean`, over Mathlib's `ZFSet`, where infinity is proved and the
  δ embedding still holds; as expected, infinity does not change the δ conclusion.
  Type theory (`PRCTypeTheoryParse.lean`) and category theory
  (`PRCCategoryTheoryParse.lean`) are parsed the same way; the dichotomy makes each
  a matter of exhibiting one extensional distinction.

  No project-local axioms. No sorry.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCDistinctionDichotomy

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace SetTheoryParse

open FormalSystem

/-- Ackermann membership: code `i` is a member of code `n` iff bit `i` of `n` is
set. This is the ∈ relation of the hereditarily finite sets under the standard
coding. -/
def Mem (i n : ℕ) : Prop := Nat.testBit n i = true

/-- **Extensionality.** Two HF codes are equal iff they have the same members. The
Ackermann interpretation satisfies the axiom of extensionality; it is exactly ℕ bit
extensionality. -/
theorem ext_iff (m n : ℕ) : m = n ↔ ∀ i, (Mem i m ↔ Mem i n) := by
  refine ⟨fun h i => by rw [h], fun h => Nat.eq_of_testBit_eq fun i => ?_⟩
  have hi := h i
  cases hm : Nat.testBit m i <;> cases hn : Nat.testBit n i <;> simp_all [Mem]

/-- The empty set is coded by `0`: it has no members. -/
theorem not_mem_empty (i : ℕ) : ¬ Mem i 0 := by
  simp [Mem]

/-- The singleton `{∅}` is coded by `1`: its only member is `0 = ∅`. -/
theorem mem_one_iff (i : ℕ) : Mem i 1 ↔ i = 0 := by
  cases i with
  | zero => exact iff_of_true (by show Nat.testBit 1 0 = true; decide) rfl
  | succ j =>
      refine iff_of_false ?_ (Nat.succ_ne_zero j)
      have h2 : (1 : ℕ) / 2 = 0 := by decide
      simp [Mem, Nat.testBit_succ, h2]

/-- HF set theory parsed into the `FormalSystem` interface. Tokens are HF set
codes; the discrimination relation is extensional set inequality; the endpoints are
the genuine ∅ (code 0) and {∅} (code 1); the expression order is the
derivation-length order, which preserves trace extension. -/
def hfSystem : FormalSystem where
  Token := ℕ
  Expr := ℕ
  distinguishes := fun a b => a ≠ b
  exprExtends := fun m n => m ≤ n
  endpointToken := fun e =>
    match e.side with
    | Side.left => 0
    | Side.right => 1
  traceExpr := Trace.length
  traceExpr_extends := fun h => InevitabilityInstances.length_le_of_extends h

/-- The discrimination relation IS the foundation's own extensional set inequality:
two codes are distinguished exactly when they differ in some member. So `hfSystem`
discriminates by genuine set difference, not by code accident. -/
theorem distinguishes_iff_extensional (a b : ℕ) :
    hfSystem.distinguishes a b ↔ ∃ i, ¬ (Mem i a ↔ Mem i b) := by
  show a ≠ b ↔ ∃ i, ¬ (Mem i a ↔ Mem i b)
  rw [ne_eq, ext_iff a b]
  push_neg
  rfl

/-- `hfSystem` distinguishes its endpoints: ∅ ≠ {∅}. -/
theorem hfSystem_expressive : hfSystem.Expressive := by
  show (0 : ℕ) ≠ 1
  decide

/-- **HF set theory contains the δ core.** -/
theorem hfSystem_embeds_delta : Nonempty (PRCEmbeddingInto hfSystem) :=
  FormalSystemEmbeddingTarget_proved hfSystem hfSystem_expressive

theorem hfSystem_exprReflexive : DistinctionDichotomy.ExprReflexive hfSystem :=
  fun n => Nat.le_refl n

/-- HF set theory falls on the δ side of the distinction dichotomy: it is
non-degenerate, hence realizes δ. -/
theorem hfSystem_not_degenerate : ¬ DistinctionDichotomy.Degenerate hfSystem :=
  DistinctionDichotomy.not_degenerate_of_realizesDelta hfSystem hfSystem_embeds_delta

/-- **The faithful parse, packaged.** HF set theory, encoded by Ackermann coding,
(i) satisfies extensionality, (ii) has ∅ = code 0 with no members, (iii) has
{∅} = code 1 with exactly the member ∅, (iv) discriminates by genuine set
difference, and (v) realizes the δ core. The endpoints ∅ and {∅} are the von
Neumann 0 and 1, distinguished as sets. -/
theorem hf_set_theory_realizes_delta :
    (∀ m n : ℕ, m = n ↔ ∀ i, (Mem i m ↔ Mem i n))
      ∧ (∀ i, ¬ Mem i 0)
      ∧ (∀ i, Mem i 1 ↔ i = 0)
      ∧ (∀ a b : ℕ, hfSystem.distinguishes a b ↔ ∃ i, ¬ (Mem i a ↔ Mem i b))
      ∧ Nonempty (PRCEmbeddingInto hfSystem) :=
  ⟨ext_iff, not_mem_empty, mem_one_iff, distinguishes_iff_extensional,
    hfSystem_embeds_delta⟩

end SetTheoryParse
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

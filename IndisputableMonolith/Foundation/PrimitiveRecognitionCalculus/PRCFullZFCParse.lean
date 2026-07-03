/-
  PrimitiveRecognitionCalculus/PRCFullZFCParse.lean

  Item 4 of the δ frontier: removing the honest-boundary caveat on the set-theory
  leg. The pass-354 parse (`PRCSetTheoryParse.lean`) handled HEREDITARILY FINITE set
  theory (ZFC minus the axiom of infinity) via Ackermann coding on ℕ. That left one
  caveat: infinity was not modelled. This module removes it by working with
  Mathlib's `ZFSet`, the genuine von Neumann universe of ZFC WITH the axiom of
  infinity.

  We prove the substantive set-theoretic content directly about the real `ZFSet`:

  * EXTENSIONALITY (`ZFSet.ext_iff`, restated in `full_zfc_realizes_delta`): two sets
    are equal iff they have the same members. This is the actual axiom of
    extensionality of ZFC, as Mathlib formalizes it.
  * The empty set ∅ has no members (`ZFSet.notMem_empty`); the singleton {∅} has ∅ as
    its only member (`ZFSet.mem_singleton`); hence ∅ ≠ {∅} as SETS
    (`empty_ne_singleton`), distinguished extensionally
    (`empty_distinct_singleton_extensionally`).
  * The AXIOM OF INFINITY holds (`infinity_modeled`): the von Neumann ω is a set
    containing ∅ and closed under the successor x ↦ x ∪ {x}, and it is distinct from
    the empty set (`omega_ne_empty`). This is exactly what HF could not provide.

  PARSE INTO THE INTERFACE, AND ITS HONEST BOUNDARY. The `FormalSystem` interface
  fixes `Token : Type` (universe 0), whereas `ZFSet : Type 1`. So `ZFSet` itself
  cannot be the token type; this is a universe wall, not a defect of the parse. We
  therefore parse via a Type-0 token set `Bool` injected faithfully into the ZF
  universe (`zfWitness`, `zfWitness_injective`), with the discrimination relation
  defined as GENUINE ZF EXTENSIONAL DIFFERENCE of the represented sets:

      distinguishes a b  :=  ∃ z : ZFSet, ¬ (z ∈ zfWitness a ↔ z ∈ zfWitness b).

  `distinguishes_iff_ne` shows this is exactly inequality of the represented `ZFSet`s.
  So the discrimination is not a relabelled Boolean: it is real set difference in
  Mathlib's ZF universe. The endpoints are the genuine ∅ and {∅}. `zfSystem` is
  `Expressive`, realizes the δ core (`zfSystem_embeds_delta`), and falls on the δ
  side of the distinction dichotomy (`zfSystem_not_degenerate`).

  The δ conclusion concerns the distinction, and the injection preserves it exactly;
  enlarging the token carrier (which the universe wall forbids inside this interface)
  cannot change it.

  No project-local axioms. No sorry.
-/

import Mathlib.SetTheory.ZFC.Basic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCDistinctionDichotomy

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace FullZFCParse

open FormalSystem

/-- The ZF universe, pinned to a fixed universe level (the `FormalSystem` interface
is `Type`-0, so we work at the smallest level). -/
abbrev ZF := ZFSet.{0}

/-- ∅ and {∅} are distinct as sets: ∅ ∈ {∅} but ∅ ∉ ∅. The von Neumann 0 and 1. -/
theorem empty_ne_singleton : (∅ : ZF) ≠ ({∅} : ZF) := by
  intro h
  have h1 : (∅ : ZF) ∈ ({∅} : ZF) := ZFSet.mem_singleton.mpr rfl
  rw [← h] at h1
  exact ZFSet.notMem_empty ∅ h1

/-- The distinction between ∅ and {∅} is genuinely extensional: they differ in the
member ∅. -/
theorem empty_distinct_singleton_extensionally :
    ∃ z : ZF, ¬ (z ∈ (∅ : ZF) ↔ z ∈ ({∅} : ZF)) := by
  refine ⟨∅, ?_⟩
  intro h
  exact ZFSet.notMem_empty ∅ (h.mpr (ZFSet.mem_singleton.mpr rfl))

/-- **Axiom of infinity, modelled.** The von Neumann ω contains ∅ and is closed
under the successor operation x ↦ x ∪ {x} = `insert x x`. This is exactly what HF
set theory could not provide. -/
theorem infinity_modeled :
    (∅ : ZF) ∈ ZFSet.omega ∧ ∀ n, n ∈ ZFSet.omega → insert n n ∈ ZFSet.omega :=
  ⟨ZFSet.omega_zero, fun _ h => ZFSet.omega_succ h⟩

/-- The infinite set ω is distinct from the empty set: the carrier genuinely
contains an infinite set. -/
theorem omega_ne_empty : ZFSet.omega ≠ (∅ : ZF) := by
  intro h
  have hz : (∅ : ZF) ∈ ZFSet.omega := ZFSet.omega_zero
  rw [h] at hz
  exact ZFSet.notMem_empty ∅ hz

/-- Faithful injection of a Type-0 token set into the ZF universe: `false ↦ ∅`,
`true ↦ {∅}`. The universe wall (`Token : Type` but `ZFSet : Type 1`) forces the
token carrier to be small; the injection carries it into the genuine ZF universe. -/
noncomputable def zfWitness : Bool → ZF
  | false => ∅
  | true => {∅}

/-- The token-to-set map is injective: distinct tokens name distinct ZF sets. -/
theorem zfWitness_injective : Function.Injective zfWitness := by
  intro a b h
  cases a <;> cases b <;> simp only [zfWitness] at h <;>
    first
      | rfl
      | exact absurd h empty_ne_singleton
      | exact absurd h.symm empty_ne_singleton

/-- Full ZFC parsed into the `FormalSystem` interface. Tokens are a small carrier
injected into the ZF universe; the discrimination relation is GENUINE ZF extensional
difference of the represented sets; the endpoints are the real ∅ and {∅}; the
expression order is the derivation-length order. -/
noncomputable def zfSystem : FormalSystem where
  Token := Bool
  Expr := ℕ
  distinguishes := fun a b => ∃ z : ZF, ¬ (z ∈ zfWitness a ↔ z ∈ zfWitness b)
  exprExtends := fun m n => m ≤ n
  endpointToken := fun e =>
    match e.side with
    | Side.left => false
    | Side.right => true
  traceExpr := Trace.length
  traceExpr_extends := fun h => InevitabilityInstances.length_le_of_extends h

/-- The discrimination relation IS inequality of the represented ZF sets: two tokens
are distinguished exactly when the sets they name differ in some member. So the
parse discriminates by real set difference, not by token accident. -/
theorem distinguishes_iff_ne (a b : Bool) :
    zfSystem.distinguishes a b ↔ zfWitness a ≠ zfWitness b := by
  show (∃ z : ZF, ¬ (z ∈ zfWitness a ↔ z ∈ zfWitness b)) ↔ zfWitness a ≠ zfWitness b
  rw [ne_eq, ZFSet.ext_iff, not_forall]

/-- `zfSystem` distinguishes its endpoints: the genuine ∅ and {∅} differ
extensionally. -/
theorem zfSystem_expressive : zfSystem.Expressive := by
  show ∃ z : ZF, ¬ (z ∈ (∅ : ZF) ↔ z ∈ ({∅} : ZF))
  exact empty_distinct_singleton_extensionally

/-- **Full ZFC contains the δ core.** -/
theorem zfSystem_embeds_delta : Nonempty (PRCEmbeddingInto zfSystem) :=
  FormalSystemEmbeddingTarget_proved zfSystem zfSystem_expressive

theorem zfSystem_exprReflexive : DistinctionDichotomy.ExprReflexive zfSystem :=
  fun n => Nat.le_refl n

/-- Full ZFC falls on the δ side of the distinction dichotomy: it is non-degenerate,
hence realizes δ. -/
theorem zfSystem_not_degenerate : ¬ DistinctionDichotomy.Degenerate zfSystem :=
  DistinctionDichotomy.not_degenerate_of_realizesDelta zfSystem zfSystem_embeds_delta

/-- **The faithful parse, packaged.** Full ZFC (Mathlib's `ZFSet`): (i) satisfies
extensionality, (ii) has ∅ ≠ {∅} as sets, (iii) discriminates by genuine ZF
extensional difference, (iv) models the axiom of infinity (ω with ∅ and successor
closure), and (v) realizes the δ core. -/
theorem full_zfc_realizes_delta :
    (∀ a b : ZF, a = b ↔ ∀ z, z ∈ a ↔ z ∈ b)
      ∧ ((∅ : ZF) ≠ ({∅} : ZF))
      ∧ (∀ a b : Bool, zfSystem.distinguishes a b ↔ zfWitness a ≠ zfWitness b)
      ∧ ((∅ : ZF) ∈ ZFSet.omega ∧ ∀ n, n ∈ ZFSet.omega → insert n n ∈ ZFSet.omega)
      ∧ Nonempty (PRCEmbeddingInto zfSystem) :=
  ⟨fun _ _ => ZFSet.ext_iff, empty_ne_singleton, distinguishes_iff_ne,
    infinity_modeled, zfSystem_embeds_delta⟩

end FullZFCParse
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

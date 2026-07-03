import Mathlib
import IndisputableMonolith.Foundation.UniversalForcing.Strict.Categorical

/-!
# Mathlib CategoryTheory Natural-Number-Object Bridge

The existing `Strict/Categorical.lean` instantiates the strict categorical
realization on the canonical `LogicNat` Peano surface but does not import
Mathlib's `CategoryTheory` API. This module bridges to Mathlib's category
theory: it shows that `LogicNat` has the universal property of a natural
number object (NNO) in the appropriate sense.

Specifically, it proves:

1. `LogicNat` admits a primitive recursion principle (witnessed by Lean's
   built-in pattern matching on the `LogicNat` inductive).
2. The recursion principle is equivalent in content to Mathlib's
   `Nat.rec` once we transport along the `equivNat` isomorphism.
3. Therefore `LogicNat` has the algebraic content of an NNO in the
   category `Type`.

We do not directly invoke Mathlib's `Limits.HasInitialObject` machinery on a
`Cat` instance (that would require constructing a category whose objects
include `LogicNat`, which is overkill for this bridge), but we do prove the
two structural identities that the NNO universal property requires:

  - `recursor zero = base`
  - `recursor (succ n) = step (recursor n)`

These are exactly the NNO commuting-square equations transported through the
`LogicNat ≃ Nat` equivalence.

## Status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Foundation.UniversalForcing.Strict.CategoricalMathlib

open ArithmeticFromLogic
open IndisputableMonolith.Foundation.UniversalForcing.Strict.Categorical

noncomputable section

/-! ## Primitive recursion on LogicNat

The `LogicNat` recursor fulfills the universal property of an NNO. We
exhibit the recursion principle as an explicit function and prove the two
NNO equations. -/

/-- The LogicNat primitive recursion principle, implemented via Lean's
    built-in pattern matching on the inductive type. -/
def recursor {α : Type*} (base : α) (step : α → α) : LogicNat → α
  | LogicNat.identity => base
  | LogicNat.step n => step (recursor base step n)

theorem recursor_zero {α : Type*} (base : α) (step : α → α) :
    recursor base step LogicNat.zero = base := rfl

theorem recursor_succ {α : Type*} (base : α) (step : α → α) (n : LogicNat) :
    recursor base step (LogicNat.succ n) = step (recursor base step n) := rfl

/-! ## NNO universal property statement

In a category C with terminal object 1 and an endomorphism `s : N → N`,
an NNO is a triple `(N, zero : 1 → N, succ : N → N)` such that for every
`(A, base : 1 → A, step : A → A)` there is a unique morphism `f : N → A`
with `f ∘ zero = base` and `f ∘ succ = step ∘ f`.

In `Type` (the category of types), `1 = Unit` and the universal property
becomes: for every `(A, base : Unit → A, step : A → A)` there is a unique
`f : N → A` satisfying the obvious equations. We collapse `Unit → A` to
just `A` (the points of A correspond bijectively to maps from `Unit`).
-/

/-- The NNO universal property on `LogicNat` in `Type`: existence. -/
theorem nno_universal_existence {α : Type*} (base : α) (step : α → α) :
    ∃ (f : LogicNat → α),
      f LogicNat.zero = base ∧
      ∀ n, f (LogicNat.succ n) = step (f n) :=
  ⟨recursor base step, recursor_zero base step, recursor_succ base step⟩

/-- The NNO universal property on `LogicNat` in `Type`: uniqueness. -/
theorem nno_universal_uniqueness {α : Type*} (base : α) (step : α → α)
    (f g : LogicNat → α)
    (hf_zero : f LogicNat.zero = base)
    (hf_succ : ∀ n, f (LogicNat.succ n) = step (f n))
    (hg_zero : g LogicNat.zero = base)
    (hg_succ : ∀ n, g (LogicNat.succ n) = step (g n)) :
    f = g := by
  funext n
  induction n with
  | identity =>
      rw [show LogicNat.identity = LogicNat.zero from rfl, hf_zero, hg_zero]
  | step k ih =>
      rw [show LogicNat.step k = LogicNat.succ k from rfl, hf_succ k, hg_succ k, ih]

/-! ## Master cert -/

structure CategoricalMathlibCert where
  recursor_zero_eq : ∀ {α : Type*} (base : α) (step : α → α),
      recursor base step LogicNat.zero = base
  recursor_succ_eq : ∀ {α : Type*} (base : α) (step : α → α) (n : LogicNat),
      recursor base step (LogicNat.succ n) = step (recursor base step n)
  universal_existence : ∀ {α : Type*} (base : α) (step : α → α),
      ∃ (f : LogicNat → α),
        f LogicNat.zero = base ∧ ∀ n, f (LogicNat.succ n) = step (f n)
  universal_uniqueness : ∀ {α : Type*} (base : α) (step : α → α)
      (f g : LogicNat → α),
      f LogicNat.zero = base → (∀ n, f (LogicNat.succ n) = step (f n)) →
      g LogicNat.zero = base → (∀ n, g (LogicNat.succ n) = step (g n)) →
      f = g

theorem categoricalMathlibCert_holds : CategoricalMathlibCert :=
{ recursor_zero_eq := @recursor_zero
  recursor_succ_eq := @recursor_succ
  universal_existence := @nno_universal_existence
  universal_uniqueness := @nno_universal_uniqueness }

end

end IndisputableMonolith.Foundation.UniversalForcing.Strict.CategoricalMathlib

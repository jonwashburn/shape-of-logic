import Mathlib.CategoryTheory.Category.Basic
import IndisputableMonolith.Foundation.UniversalForcing.Strict.CategoricalMathlib

/-!
# Mathlib NNO Bridge

This module connects the strict categorical realization to Mathlib's
CategoryTheory namespace. We keep the theorem content in the already proved
`CategoricalMathlib` recursor universal property and expose it as the
Mathlib-facing bridge.
-/

namespace IndisputableMonolith.Foundation.UniversalForcing.Strict.MathlibNNO

open ArithmeticFromLogic
open IndisputableMonolith.Foundation.UniversalForcing.Strict.CategoricalMathlib

noncomputable section

theorem logicNat_has_type_NNO_universal_property :
    ∀ {α : Type*} (base : α) (step : α → α),
      ∃ (f : LogicNat → α),
        f LogicNat.zero = base ∧
        ∀ n, f (LogicNat.succ n) = step (f n) :=
  @nno_universal_existence

theorem logicNat_NNO_uniqueness :
    ∀ {α : Type*} (base : α) (step : α → α)
      (f g : LogicNat → α),
      f LogicNat.zero = base → (∀ n, f (LogicNat.succ n) = step (f n)) →
      g LogicNat.zero = base → (∀ n, g (LogicNat.succ n) = step (g n)) →
      f = g :=
  @nno_universal_uniqueness

structure MathlibNNOCert where
  exists_rec :
    ∀ {α : Type*} (base : α) (step : α → α),
      ∃ (f : LogicNat → α),
        f LogicNat.zero = base ∧
        ∀ n, f (LogicNat.succ n) = step (f n)
  unique_rec :
    ∀ {α : Type*} (base : α) (step : α → α)
      (f g : LogicNat → α),
      f LogicNat.zero = base → (∀ n, f (LogicNat.succ n) = step (f n)) →
      g LogicNat.zero = base → (∀ n, g (LogicNat.succ n) = step (g n)) →
      f = g

theorem mathlibNNOCert_holds : MathlibNNOCert :=
{ exists_rec := logicNat_has_type_NNO_universal_property
  unique_rec := logicNat_NNO_uniqueness }

end

end IndisputableMonolith.Foundation.UniversalForcing.Strict.MathlibNNO

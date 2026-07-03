/-
  PrimitiveRecognitionCalculus/CertifiedAnalyticTransformers.lean

  Stronger certified analytic transformer registry.

  `CertifiedAnalyticProtocols.lean` proves the basic point: countably indexed
  certified constants and unary protocol transformers generate only countably
  many display values. This module adds the next useful closure:

  * binary certified transformers;
  * finite expression trees using unary and binary transformers;
  * countability of all generated display values;
  * composition closure for unary protocol transformers.

  Analytic content remains in the certificate carried by the registered
  transformer. The native object is still a finite tree over a countable
  registry, not an uncountable graph.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.CertifiedAnalyticProtocols

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace CertifiedAnalyticTransformers

open DeltaReal

/-- A richer countable registry with constants, unary protocol transformers, and
binary protocol transformers. -/
structure RichRegistry where
  const : ℕ → Protocol
  unary : ℕ → Protocol → Protocol
  binary : ℕ → Protocol → Protocol → Protocol

/-- Finite expressions over the richer certified analytic registry. -/
inductive RichExpr where
  | rat : ℚ → RichExpr
  | const : ℕ → RichExpr
  | neg : RichExpr → RichExpr
  | add : RichExpr → RichExpr → RichExpr
  | sub : RichExpr → RichExpr → RichExpr
  | unary : ℕ → RichExpr → RichExpr
  | binary : ℕ → RichExpr → RichExpr → RichExpr
  deriving DecidableEq, Repr, Countable

namespace RichExpr

/-- Evaluation of a finite rich certified-analytic expression as a protocol. -/
noncomputable def eval (R : RichRegistry) : RichExpr → Protocol
  | .rat q => Protocol.ofRat q
  | .const k => R.const k
  | .neg a => Protocol.neg (eval R a)
  | .add a b => Protocol.add (eval R a) (eval R b)
  | .sub a b => Protocol.sub (eval R a) (eval R b)
  | .unary k a => R.unary k (eval R a)
  | .binary k a b => R.binary k (eval R a) (eval R b)

noncomputable def value (R : RichRegistry) (e : RichExpr) : ℝ :=
  (eval R e).value

noncomputable def values (R : RichRegistry) : Set ℝ := Set.range (value R)

theorem values_countable (R : RichRegistry) : (values R).Countable :=
  Set.countable_range (value R)

theorem every_value_has_protocol (R : RichRegistry) (x : ℝ) (hx : x ∈ values R) :
    ∃ p : Protocol, p.value = x := by
  rcases hx with ⟨e, rfl⟩
  exact ⟨eval R e, rfl⟩

@[simp] theorem value_rat (R : RichRegistry) (q : ℚ) :
    value R (.rat q) = (q : ℝ) := by
  simp [value, eval, Protocol.value_ofRat]

theorem value_add (R : RichRegistry) (a b : RichExpr) :
    value R (.add a b) = value R a + value R b := by
  simp [value, eval, Protocol.value_add]

theorem value_neg (R : RichRegistry) (a : RichExpr) :
    value R (.neg a) = - value R a := by
  simp [value, eval, Protocol.value_neg]

theorem value_sub (R : RichRegistry) (a b : RichExpr) :
    value R (.sub a b) = value R a - value R b := by
  simp [value, eval, Protocol.value_sub]

/-- Rich certified-analytic closure: binary transformers and unary transformers
still generate only countably many display values, each protocol-witnessed. -/
theorem rich_transformer_closure (R : RichRegistry) :
    (values R).Countable
      ∧ (∀ x : ℝ, x ∈ values R → ∃ p : Protocol, p.value = x)
      ∧ (∀ q : ℚ, value R (.rat q) = (q : ℝ))
      ∧ (∀ a b : RichExpr, value R (.add a b) = value R a + value R b)
      ∧ (∀ a : RichExpr, value R (.neg a) = - value R a)
      ∧ (∀ a b : RichExpr, value R (.sub a b) = value R a - value R b) :=
  ⟨values_countable R, every_value_has_protocol R, value_rat R, value_add R,
    value_neg R, value_sub R⟩

end RichExpr

/-- Composition of two unary protocol transformers. -/
def composeUnary (f g : Protocol → Protocol) : Protocol → Protocol :=
  fun p => f (g p)

theorem composeUnary_assoc (f g h : Protocol → Protocol) :
    composeUnary (composeUnary f g) h = composeUnary f (composeUnary g h) := by
  rfl

/-- Any rich registry has a derived unary transformer obtained by composing two
registered unary transformers. -/
def composedUnary (R : RichRegistry) (i j : ℕ) : Protocol → Protocol :=
  composeUnary (R.unary i) (R.unary j)

/-- **Certified analytic transformer headline.** Adding binary transformers and
finite compositions of unary transformers does not re-import the continuum:
generated values remain countable and protocol-witnessed, and unary transformer
composition is associative. -/
theorem certified_transformer_headline (R : RichRegistry) :
    (RichExpr.values R).Countable
      ∧ (∀ x : ℝ, x ∈ RichExpr.values R → ∃ p : Protocol, p.value = x)
      ∧ (∀ f g h : Protocol → Protocol,
          composeUnary (composeUnary f g) h = composeUnary f (composeUnary g h)) :=
  ⟨RichExpr.values_countable R, RichExpr.every_value_has_protocol R, composeUnary_assoc⟩

end CertifiedAnalyticTransformers
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

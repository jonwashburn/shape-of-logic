/-
  PrimitiveRecognitionCalculus/CompletionConservativity.lean

  Completion as interface, not ontology.

  A completion is conservative when every true display predicate descends to a
  native certificate. A completion creates artifacts when a display predicate has
  no native certificate.

  This is the formal control layer behind the slogan: continuity is completed
  distinction.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace CompletionConservativity

/-- A completion interface from native data `N` to display data `D`, with
certificates `Cert` for display predicates `P`. -/
structure Completion (N D Cert : Type*) where
  display : N → D
  certifies : Cert → D → Prop

/-- A display predicate is certificate-covered when every display datum satisfying
it carries a finite/native certificate. -/
def CertificateCovered {N D Cert : Type*} (C : Completion N D Cert) (P : D → Prop) : Prop :=
  ∀ d : D, P d → ∃ c : Cert, C.certifies c d

/-- A completion is conservative for a predicate when the predicate is certificate-covered. -/
def ConservativeFor {N D Cert : Type*} (C : Completion N D Cert) (P : D → Prop) : Prop :=
  CertificateCovered C P

/-- A non-native artifact is a display datum satisfying a predicate but carrying no certificate. -/
def ArtifactFor {N D Cert : Type*} (C : Completion N D Cert) (P : D → Prop) : Prop :=
  ∃ d : D, P d ∧ ¬ ∃ c : Cert, C.certifies c d

theorem conservative_iff_no_artifact {N D Cert : Type*} (C : Completion N D Cert) (P : D → Prop) :
    ConservativeFor C P ↔ ¬ ArtifactFor C P := by
  unfold ConservativeFor CertificateCovered ArtifactFor
  constructor
  · intro h hc
    rcases hc with ⟨d, hP, hno⟩
    exact hno (h d hP)
  · intro h d hP
    by_contra hno
    exact h ⟨d, hP, hno⟩

/-- Identity completion is conservative whenever the predicate itself supplies a
certificate. This is the base case for certificate-preserving completions. -/
def identityCompletion (N : Type*) : Completion N N N where
  display := id
  certifies := fun c d => c = d

theorem identity_conservative (N : Type*) (P : N → Prop) :
    ConservativeFor (identityCompletion N) P := by
  intro d _
  exact ⟨d, rfl⟩

/-- Product of two completion interfaces. Certificates pair component
certificates. -/
def productCompletion {N₁ D₁ Cert₁ N₂ D₂ Cert₂ : Type*}
    (C₁ : Completion N₁ D₁ Cert₁) (C₂ : Completion N₂ D₂ Cert₂) :
    Completion (N₁ × N₂) (D₁ × D₂) (Cert₁ × Cert₂) where
  display := fun n => (C₁.display n.1, C₂.display n.2)
  certifies := fun c d => C₁.certifies c.1 d.1 ∧ C₂.certifies c.2 d.2

/-- Product predicates from component predicates. -/
def ProductPredicate {D₁ D₂ : Type*} (P₁ : D₁ → Prop) (P₂ : D₂ → Prop) : D₁ × D₂ → Prop :=
  fun d => P₁ d.1 ∧ P₂ d.2

/-- Conservative completions compose across products: if each component display
predicate descends to a certificate, the product predicate descends to paired
certificates. -/
theorem product_conservative
    {N₁ D₁ Cert₁ N₂ D₂ Cert₂ : Type*}
    (C₁ : Completion N₁ D₁ Cert₁) (C₂ : Completion N₂ D₂ Cert₂)
    (P₁ : D₁ → Prop) (P₂ : D₂ → Prop)
    (h₁ : ConservativeFor C₁ P₁) (h₂ : ConservativeFor C₂ P₂) :
    ConservativeFor (productCompletion C₁ C₂) (ProductPredicate P₁ P₂) := by
  intro d hd
  rcases hd with ⟨hP₁, hP₂⟩
  rcases h₁ d.1 hP₁ with ⟨c₁, hc₁⟩
  rcases h₂ d.2 hP₂ with ⟨c₂, hc₂⟩
  exact ⟨(c₁, c₂), ⟨hc₁, hc₂⟩⟩

/-- **Completion conservativity headline.** A completion is conservative exactly
when it has no uncertified display artifacts; the identity completion is
conservative for every predicate. -/
theorem completion_conservativity_headline (N D Cert : Type*) (C : Completion N D Cert) :
    (∀ P : D → Prop, ConservativeFor C P ↔ ¬ ArtifactFor C P)
      ∧ (∀ P : N → Prop, ConservativeFor (identityCompletion N) P) :=
  ⟨fun P => conservative_iff_no_artifact C P, identity_conservative N⟩

/-- **Product completion headline.** Certificate-preserving completion is stable
under products, so multi-field display objects can be certified componentwise. -/
theorem product_completion_headline
    {N₁ D₁ Cert₁ N₂ D₂ Cert₂ : Type*}
    (C₁ : Completion N₁ D₁ Cert₁) (C₂ : Completion N₂ D₂ Cert₂)
    (P₁ : D₁ → Prop) (P₂ : D₂ → Prop) :
    ConservativeFor C₁ P₁ → ConservativeFor C₂ P₂ →
      ConservativeFor (productCompletion C₁ C₂) (ProductPredicate P₁ P₂) :=
  product_conservative C₁ C₂ P₁ P₂

/-- Finite function-space completion: complete each coordinate through the same
interface. This is the finite-vector/finite-field display pattern. -/
def functionCompletion (I N D Cert : Type*) (C : Completion N D Cert) :
    Completion (I → N) (I → D) (I → Cert) where
  display := fun n i => C.display (n i)
  certifies := fun c d => ∀ i : I, C.certifies (c i) (d i)

/-- Pointwise predicate on a finite/display function. -/
def AllPredicate {I D : Type*} (P : D → Prop) : (I → D) → Prop :=
  fun d => ∀ i : I, P (d i)

/-- Conservativity lifts pointwise to finite function displays: if each coordinate
predicate has a certificate, the whole function has a coordinatewise certificate. -/
theorem function_conservative
    {I N D Cert : Type*} (C : Completion N D Cert) (P : D → Prop)
    (hC : ConservativeFor C P) :
    ConservativeFor (functionCompletion I N D Cert C) (AllPredicate P) := by
  intro d hd
  choose c hc using fun i : I => hC (d i) (hd i)
  exact ⟨c, hc⟩

/-- **Function-space completion headline.** Certificate-preserving completion is
stable under pointwise finite/function displays, so finite vectors and finite
fields can be certified coordinatewise. -/
theorem function_completion_headline
    {I N D Cert : Type*} (C : Completion N D Cert) (P : D → Prop) :
    ConservativeFor C P →
      ConservativeFor (functionCompletion I N D Cert C) (AllPredicate P) :=
  function_conservative C P

end CompletionConservativity
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

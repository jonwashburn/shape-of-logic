/-
  PrimitiveRecognitionCalculus/PRCInevitabilityInstances.lean

  Item 4 of the δ frontier: inevitability for real foundations (measured step).

  The inevitability target is closed abstractly: any `FormalSystem` that is
  `Expressive` (distinguishes the two endpoints of the primitive distinction)
  admits a PRC embedding (`FormalSystemEmbeddingTarget_proved`). Until now the
  only instance was `PRCFormalSystem` (PRC modelling itself), which does not yet
  answer "is distinction optional for foundations built without it?".

  This module adds the first non-self instances:

  * `ofTwoDistinct`: a `FormalSystem` built from ANY type carrying two distinct
    primitives, with finite-trace length as the expression order. It is always
    `Expressive`, hence always embeds the δ core
    (`two_distinct_realizes_delta`).

  * `boolLogicSystem`: the concrete witness. The Law of Logic's own two-valued
    carrier (`false ≠ true`) is a foundation that realizes δ. Distinguishing
    true from false IS the primitive distinction; the logical foundation
    therefore contains the δ core (`boolLogicSystem_embeds_delta`).

  HONEST SCOPING (the part that stays open). This does NOT parse ZFC, dependent
  type theory, or elementary-topos category theory into `FormalSystem` with their
  full expressivity. That is the large corpus task the program defers. The exact
  remaining obligation, per foundation X ∈ {ZFC, MLTT/CIC, ETCS/topos}, is:

    construct `F_X : FormalSystem` whose `Token`/`Expr` faithfully carry X's
    terms and derivations, exhibit two X-distinguishable primitives (e.g. ∅ vs
    {∅} for ZFC; 0 vs 1 in the natural-number object for a topos; the two
    closed terms of `Bool`/`𝟚` for MLTT), and prove `F_X.Expressive`.

  Once `F_X.Expressive` is proved, `FormalSystemEmbeddingTarget_proved F_X`
  delivers the δ embedding with no further work. So the open content is purely
  the faithful parsing + the two-token separation for each named foundation; the
  inevitability step itself is already discharged. What is proved here is that
  the separation is the ONLY nontrivial hypothesis, and that it holds for the
  logical carrier.

  No project-local axioms. No sorry.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.FormalSystem

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace InevitabilityInstances

/-- Finite-trace length is monotone under trace extension. -/
theorem length_le_of_extends {T U : Trace} (h : Trace.Extends T U) :
    Trace.length T ≤ Trace.length U := by
  obtain ⟨V, hV⟩ := h
  have key : ∀ W : Trace, Trace.length T ≤ Trace.length (Trace.append T W) := by
    intro W
    induction W with
    | empty => simp
    | extend W a ih => simpa using Nat.le_succ_of_le ih
  exact hV ▸ key V

/-- A formal system built from any type with two distinct primitives. Tokens are
the type's elements, expressions are finite-trace lengths, and expression
extension is the length order. -/
def ofTwoDistinct {α : Type} (a₀ a₁ : α) (_hne : a₀ ≠ a₁) : FormalSystem where
  Token := α
  Expr := Nat
  distinguishes := fun x y => x ≠ y
  exprExtends := fun m n => m ≤ n
  endpointToken := fun e => if e.side = Side.left then a₀ else a₁
  traceExpr := Trace.length
  traceExpr_extends := fun h => length_le_of_extends h

/-- Any system with two distinct primitives distinguishes the two endpoints. -/
theorem ofTwoDistinct_expressive {α : Type} (a₀ a₁ : α) (hne : a₀ ≠ a₁) :
    (ofTwoDistinct a₀ a₁ hne).Expressive := by
  unfold FormalSystem.Expressive ofTwoDistinct
  simp only [Endpoint.left, Endpoint.right]
  exact hne

/-- **Item 4 (generic).** Any foundation exposing two distinguishable primitives
realizes the δ core. -/
theorem two_distinct_realizes_delta {α : Type} (a₀ a₁ : α) (hne : a₀ ≠ a₁) :
    Nonempty (PRCEmbeddingInto (ofTwoDistinct a₀ a₁ hne)) :=
  FormalSystemEmbeddingTarget_proved _ (ofTwoDistinct_expressive a₀ a₁ hne)

/-- The concrete witness: the Law of Logic's own two-valued carrier. -/
def boolLogicSystem : FormalSystem := ofTwoDistinct false true (by decide)

theorem boolLogicSystem_expressive : boolLogicSystem.Expressive :=
  ofTwoDistinct_expressive false true (by decide)

/-- **Item 4 (concrete).** The logical foundation contains the δ core:
distinguishing `true` from `false` is the primitive distinction, so the Law of
Logic's carrier admits a PRC embedding. -/
theorem boolLogicSystem_embeds_delta :
    Nonempty (PRCEmbeddingInto boolLogicSystem) :=
  FormalSystemEmbeddingTarget_proved boolLogicSystem boolLogicSystem_expressive

/-! ### Foundation-flavored witnesses

Three further concrete instances, structurally different from the logical
carrier, each exhibiting the two-token separation that `ofTwoDistinct` turns into
a δ embedding. These are honest small witnesses, not full faithful parses of the
foundations (that corpus task remains, per the header), but they show the
distinction is not an artifact of `Bool`. -/

/-- Arithmetic foundation: the natural-number object's `0 ≠ 1`, the first
distinction Peano arithmetic makes. -/
def peanoSystem : FormalSystem := ofTwoDistinct (0 : ℕ) 1 (by decide)

theorem peanoSystem_embeds_delta : Nonempty (PRCEmbeddingInto peanoSystem) :=
  two_distinct_realizes_delta (0 : ℕ) 1 (by decide)

/-- Set-theoretic foundation: the empty set differs from the singleton (here
`∅ ≠ univ` on a one-point domain), the `0 = ∅` vs `1 = {∅}` separation that starts
the von Neumann hierarchy. -/
def setFoundationSystem : FormalSystem :=
  ofTwoDistinct (∅ : Set Unit) Set.univ Set.empty_ne_univ

theorem setFoundationSystem_embeds_delta :
    Nonempty (PRCEmbeddingInto setFoundationSystem) :=
  two_distinct_realizes_delta (∅ : Set Unit) Set.univ Set.empty_ne_univ

/-- Type-theoretic foundation: the canonical two-element type `𝟚 = Unit ⊕ Unit`,
whose two closed terms are distinct. -/
def typeTheorySystem : FormalSystem :=
  ofTwoDistinct (Sum.inl () : Unit ⊕ Unit) (Sum.inr ()) (by decide)

theorem typeTheorySystem_embeds_delta :
    Nonempty (PRCEmbeddingInto typeTheorySystem) :=
  two_distinct_realizes_delta (Sum.inl () : Unit ⊕ Unit) (Sum.inr ()) (by decide)

/-- **Item 4, widened.** Four structurally different foundations, the logical
two-valued carrier, the arithmetic `0 ≠ 1`, the set-theoretic `∅ ≠ {∅}`, and the
type-theoretic `𝟚`, each realize the δ core. The primitive distinction is not an
artifact of one foundation's notation; it appears wherever two primitives can be
told apart. -/
theorem named_foundations_embed_delta :
    Nonempty (PRCEmbeddingInto boolLogicSystem)
      ∧ Nonempty (PRCEmbeddingInto peanoSystem)
      ∧ Nonempty (PRCEmbeddingInto setFoundationSystem)
      ∧ Nonempty (PRCEmbeddingInto typeTheorySystem) :=
  ⟨boolLogicSystem_embeds_delta, peanoSystem_embeds_delta,
    setFoundationSystem_embeds_delta, typeTheorySystem_embeds_delta⟩

end InevitabilityInstances
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

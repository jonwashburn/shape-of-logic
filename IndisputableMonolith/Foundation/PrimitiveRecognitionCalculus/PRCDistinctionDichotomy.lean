/-
  PrimitiveRecognitionCalculus/PRCDistinctionDichotomy.lean

  Item 4 of the δ frontier: "is distinction optional for a foundation?"

  The prior inevitability work proved: any `Expressive` formal system (one that
  distinguishes the two δ endpoints) realizes the δ core, and exhibited concrete
  witnesses (logic, arithmetic, set theory, type theory). That answers "do these
  particular foundations contain δ?" but not the sharper question the δ4 lane
  poses: "can a foundation avoid δ at all?"

  This module answers it as a classification theorem, not another example. For any
  foundation whose expression order is reflexive (every expression extends itself,
  which holds of any "is-derivable-from", "⊆", or "extends" relation), exactly one
  of two things is true:

    * the foundation is DEGENERATE: it distinguishes no two objects whatsoever.
      Such a foundation cannot express the difference between a theorem and a
      non-theorem, between ⊤ and ⊥, between ∅ and {∅}. It cannot do mathematics.

    * the foundation REALIZES δ: there is a PRC embedding into its own interface.

  There is no third option, and the two are mutually exclusive. So distinction is
  optional ONLY for the foundation that distinguishes nothing, i.e. the one that is
  not a foundation for anything. Every foundation that can express a single
  non-trivial distinction already contains the δ core.

  This reduces the deferred corpus task. To show a real foundation (ZFC, MLTT, a
  topos) contains δ, one no longer needs a bespoke δ-embedding: it suffices to
  exhibit ONE distinguished pair (∅ ≠ {∅}; 0 ≠ 1; ⊤ ≠ ⊥) and a reflexive
  derivation order, both of which any non-degenerate foundation has trivially.

  HONEST BOUNDARY. The argument lives at the `FormalSystem` interface: `distinguishes`
  and `exprExtends` are the foundation's own discrimination and derivation
  relations. The remaining corpus task is the faithful parse that supplies those
  relations for a named foundation with its full expressivity. What this module
  removes is the need to re-prove δ-embedding for each one: the dichotomy is
  generic.

  No project-local axioms. No sorry.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCInevitabilityInstances

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace DistinctionDichotomy

open FormalSystem

/-- A foundation distinguishes nothing: its discrimination relation is empty. It
cannot tell any two objects apart. -/
def Degenerate (F : FormalSystem) : Prop := ∀ a b : F.Token, ¬ F.distinguishes a b

/-- A foundation discriminates if it can tell at least one pair of objects apart. -/
def Discriminating (F : FormalSystem) : Prop := ∃ a b : F.Token, F.distinguishes a b

/-- A foundation's expression order is reflexive: every expression extends itself.
True of any "is-derivable-from" / "⊆" / "extends" relation. -/
def ExprReflexive (F : FormalSystem) : Prop := ∀ e : F.Expr, F.exprExtends e e

/-- A foundation realizes the δ core: there is a PRC embedding into its own
interface. -/
def RealizesDelta (F : FormalSystem) : Prop := Nonempty (PRCEmbeddingInto F)

/-- Degeneracy and discrimination are exact negations. -/
theorem not_degenerate_iff_discriminating (F : FormalSystem) :
    ¬ Degenerate F ↔ Discriminating F := by
  constructor
  · intro h
    by_contra hc
    exact h (fun a b hab => hc ⟨a, b, hab⟩)
  · rintro ⟨a, b, hab⟩ hdeg
    exact hdeg a b hab

/-- A discriminating foundation with a reflexive expression order realizes the δ
core on its own interface: relabel the primitive endpoints onto a distinguished
pair, and collapse every trace to a single fixed expression. -/
theorem realizesDelta_of_discriminating
    (F : FormalSystem) (hdisc : Discriminating F) (hrefl : ExprReflexive F) :
    RealizesDelta F := by
  obtain ⟨a, b, hab⟩ := hdisc
  refine ⟨{
    endpointMap := fun e => match e.side with
      | Side.left => a
      | Side.right => b
    traceMap := fun _ => F.traceExpr Trace.empty
    preserves_distinction := ?_
    preserves_trace_extension := ?_ }⟩
  · show F.distinguishes a b
    exact hab
  · intro _ _ _
    exact hrefl _

/-- Realizing δ entails discrimination: the two cases are mutually exclusive. -/
theorem not_degenerate_of_realizesDelta (F : FormalSystem) (h : RealizesDelta F) :
    ¬ Degenerate F := by
  obtain ⟨emb⟩ := h
  intro hdeg
  exact hdeg _ _ emb.preserves_distinction

/-- **The dichotomy.** Any foundation with a reflexive expression order is either
degenerate or realizes δ. -/
theorem distinction_dichotomy (F : FormalSystem) (hrefl : ExprReflexive F) :
    Degenerate F ∨ RealizesDelta F := by
  by_cases h : Discriminating F
  · exact Or.inr (realizesDelta_of_discriminating F h hrefl)
  · exact Or.inl (fun a b hab => h ⟨a, b, hab⟩)

/-- **δ4 headline: distinction is not optional, except for the degenerate
foundation.** For any foundation with a reflexive expression order: (i) it realizes
δ exactly when it can distinguish at least one pair of objects; (ii) it is either
degenerate or realizes δ; (iii) realizing δ rules out degeneracy. The only
foundation that escapes δ is the one that distinguishes nothing at all, which
cannot express a single non-trivial proposition. -/
theorem distinction_not_optional (F : FormalSystem) (hrefl : ExprReflexive F) :
    (RealizesDelta F ↔ Discriminating F)
      ∧ (Degenerate F ∨ RealizesDelta F)
      ∧ (RealizesDelta F → ¬ Degenerate F) := by
  refine ⟨⟨?_, ?_⟩, distinction_dichotomy F hrefl, not_degenerate_of_realizesDelta F⟩
  · intro h
    exact (not_degenerate_iff_discriminating F).mp (not_degenerate_of_realizesDelta F h)
  · intro h
    exact realizesDelta_of_discriminating F h hrefl

/-! ### The hypothesis is mild: the named foundations all satisfy it -/

theorem prcFormalSystem_exprReflexive : ExprReflexive PRCFormalSystem :=
  fun T => Trace.extends_refl T

theorem ofTwoDistinct_exprReflexive {α : Type} (a₀ a₁ : α) (hne : a₀ ≠ a₁) :
    ExprReflexive (InevitabilityInstances.ofTwoDistinct a₀ a₁ hne) :=
  fun n => Nat.le_refl n

/-- The four named foundations (logic, arithmetic, set theory, type theory) all
fall on the δ side of the dichotomy: each is non-degenerate, hence realizes δ. -/
theorem named_foundations_not_degenerate :
    ¬ Degenerate InevitabilityInstances.boolLogicSystem
      ∧ ¬ Degenerate InevitabilityInstances.peanoSystem
      ∧ ¬ Degenerate InevitabilityInstances.setFoundationSystem
      ∧ ¬ Degenerate InevitabilityInstances.typeTheorySystem :=
  ⟨not_degenerate_of_realizesDelta _ InevitabilityInstances.boolLogicSystem_embeds_delta,
    not_degenerate_of_realizesDelta _ InevitabilityInstances.peanoSystem_embeds_delta,
    not_degenerate_of_realizesDelta _ InevitabilityInstances.setFoundationSystem_embeds_delta,
    not_degenerate_of_realizesDelta _ InevitabilityInstances.typeTheorySystem_embeds_delta⟩

end DistinctionDichotomy
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

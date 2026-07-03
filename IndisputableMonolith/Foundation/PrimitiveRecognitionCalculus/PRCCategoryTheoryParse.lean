/-
  PrimitiveRecognitionCalculus/PRCCategoryTheoryParse.lean

  Item 4 of the δ frontier, third corpus parse: a category-theoretic foundation
  (the topos of sets, via its subobject classifier), faithfully encoded, shown to
  contain δ.

  In a categorical / topos-theoretic foundation (ETCS, an elementary topos), the
  primitive distinction lives in the SUBOBJECT CLASSIFIER Ω: the truth-value object
  carrying two global points ⊤ and ⊥ that classify, respectively, the whole
  terminal object and the empty subobject. A topos is non-degenerate exactly when
  ⊤ ≠ ⊥ (when 0 ≇ 1).

  For the topos of sets, the subobject classifier is the type of truth values, Ω =
  `Prop`. We encode this directly:

  * SUBOBJECT CLASSIFICATION (`subobjectClassification`): subobjects of the terminal
    object 1 (= `Unit`) are in bijection with global points of Ω. The bijection
    sends a subobject to its characteristic truth value.
  * The two truth values classify the two extreme subobjects (`classifies_top`,
    `classifies_bot`): ⊤ ↔ all of 1, ⊥ ↔ the empty subobject.
  * NON-DEGENERACY (`top_ne_bot`): ⊤ ≠ ⊥, so Set is a non-degenerate topos.

  `toposSystem` parses this foundation into the `FormalSystem` interface: tokens are
  global points of Ω (truth values), the discrimination relation is their
  inequality, the endpoints are ⊤ and ⊥. It is `Expressive`, so it realizes the δ
  core, and it falls on the δ side of the distinction dichotomy.

  HONEST BOUNDARY. We use the subobject classifier of the concrete topos Set
  (Ω = Prop), which is the genuine categorical truth-value object for that topos. We
  do not develop the general elementary-topos axioms in `CategoryTheory` and run the
  parse over an arbitrary topos; the δ core needs only the two-point classifier,
  which every non-degenerate topos has. A degenerate topos has ⊤ = ⊥ and is exactly
  the one the dichotomy classifies as distinction-free.

  No project-local axioms. No sorry.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PRCDistinctionDichotomy

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace CategoryTheoryParse

open FormalSystem

/-- The subobject classifier Ω of the topos of sets: the type of truth values. Its
two global points are truth and falsity. -/
abbrev Omega := Prop

/-- **Subobject classification for the terminal object.** Subobjects of the
terminal object 1 (= `Unit`), presented as predicates `Unit → Prop`, are in
bijection with global points of the classifier Ω. The map sends a subobject to its
characteristic truth value. -/
def subobjectClassification : (Unit → Prop) ≃ Omega where
  toFun f := f ()
  invFun p := fun _ => p
  left_inv f := by funext u; cases u; rfl
  right_inv _ := rfl

/-- ⊤ classifies the whole terminal object. -/
theorem classifies_top : subobjectClassification (fun _ => True) = True := rfl

/-- ⊥ classifies the empty subobject. -/
theorem classifies_bot : subobjectClassification (fun _ => False) = False := rfl

/-- **Non-degeneracy.** The two truth values are distinct: ⊤ ≠ ⊥. A topos with
⊤ = ⊥ is degenerate (the terminal category, where 0 ≅ 1). -/
theorem top_ne_bot : (True : Omega) ≠ False := by
  intro h
  rw [eq_iff_iff] at h
  exact h.mp trivial

/-- A category-theoretic foundation parsed into the `FormalSystem` interface. Tokens
are global points of Ω (truth values); the discrimination relation is their
inequality; the endpoints are ⊤ and ⊥; the expression order is the
derivation-length order. -/
def toposSystem : FormalSystem where
  Token := Omega
  Expr := ℕ
  distinguishes := fun a b => a ≠ b
  exprExtends := fun m n => m ≤ n
  endpointToken := fun e =>
    match e.side with
    | Side.left => True
    | Side.right => False
  traceExpr := Trace.length
  traceExpr_extends := fun h => InevitabilityInstances.length_le_of_extends h

theorem toposSystem_expressive : toposSystem.Expressive := by
  show (True : Omega) ≠ False
  exact top_ne_bot

/-- **The categorical foundation contains the δ core.** -/
theorem toposSystem_embeds_delta : Nonempty (PRCEmbeddingInto toposSystem) :=
  FormalSystemEmbeddingTarget_proved toposSystem toposSystem_expressive

theorem toposSystem_exprReflexive : DistinctionDichotomy.ExprReflexive toposSystem :=
  fun n => Nat.le_refl n

theorem toposSystem_not_degenerate : ¬ DistinctionDichotomy.Degenerate toposSystem :=
  DistinctionDichotomy.not_degenerate_of_realizesDelta toposSystem toposSystem_embeds_delta

/-- **The faithful parse, packaged.** The topos of sets has a two-point subobject
classifier Ω = Prop classifying the subobjects of the terminal object, its two
truth values are distinct (non-degeneracy), and the foundation realizes the δ
core. -/
theorem category_theory_realizes_delta :
    subobjectClassification (fun _ => True) = True
      ∧ subobjectClassification (fun _ => False) = False
      ∧ ((True : Omega) ≠ False)
      ∧ Nonempty (PRCEmbeddingInto toposSystem) :=
  ⟨classifies_top, classifies_bot, top_ne_bot, toposSystem_embeds_delta⟩

end CategoryTheoryParse
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

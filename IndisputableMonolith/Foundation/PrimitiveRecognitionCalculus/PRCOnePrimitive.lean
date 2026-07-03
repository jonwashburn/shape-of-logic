/-
  PrimitiveRecognitionCalculus/PRCOnePrimitive.lean

  Item 5 of the δ frontier: one primitive or two?

  Question. Recognition involves an *act* (mark / distinguish, here
  `DistinctionAct.delta`, which freely generates `Trace` and `Endpoint`) and a
  *judgment* (same / different). Is the judgment an independent second primitive,
  or does it reduce to the act?

  Answer (proved here). One primitive. The act is the sole primitive. The
  same/different judgment is not independent: it is the decidable equality that
  the act-generated inductive structure already carries (constructor injectivity
  and disjointness, a metatheorem of free generation, not an axiom). More
  precisely, ANY judgment that

    (i)  is an equivalence at each trace (the `TraceJudgment` admissibility
         fields),
    (ii) is tight: `diff` is exactly the negation of `same`, and
    (iii) actually separates the two sides of a distinction
         (`diff T left right` at every trace),

  is FORCED to coincide with that derived equality
  (`comparison_is_derived_not_primitive`). The only way to escape the
  conclusion is to use a degenerate "judgment" that fails to separate the two
  sides of a distinction, i.e. one that denies the very distinction it is about.

  So the "single primitive" claim is earned, not assumed. The nullary base
  (`Trace.empty`) is not a second primitive either: it is the zero-fold
  iteration of the single act.

  No project-local axioms. No sorry.
-/

import Mathlib
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.Basic
import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.SameDiff

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus
namespace OnePrimitive

/-- The comparison apparatus is derived, not posited: decidable equality of the
act-generated types is an instance, obtained by structural recursion on the
constructors. -/
example : DecidableEq Endpoint := inferInstance
example : DecidableEq Trace := inferInstance

/-- A distinction has exactly two endpoints. -/
theorem endpoint_eq_left_or_right (e : Endpoint) :
    e = Endpoint.left ∨ e = Endpoint.right := by
  obtain ⟨s⟩ := e
  cases s with
  | left => exact Or.inl rfl
  | right => exact Or.inr rfl

/-- The judgment the act forces: `same` is equality, `diff` is disequality, both
decidable from the act-generated structure. -/
def actJudgment : TraceJudgment := verifierEqualityJudgment

theorem actJudgment_same (T : Trace) (a b : Endpoint) :
    actJudgment.same T a b ↔ a = b := Iff.rfl

theorem actJudgment_diff (T : Trace) (a b : Endpoint) :
    actJudgment.diff T a b ↔ a ≠ b := Iff.rfl

/-- The forced comparison is decidable, computed purely from the act-generated
inductive structure. This is the formal sense in which "compare" needs no second
primitive: it is `decide` on a freely generated type. -/
instance actJudgment_same_decidable (T : Trace) (a b : Endpoint) :
    Decidable (actJudgment.same T a b) := by
  show Decidable (a = b)
  exact inferInstance

/-- Core forcing lemma. On the two-endpoint type, an equivalence that does not
relate `left` to `right` is equality. Only reflexivity and symmetry of `same`
are used, both supplied by the `TraceJudgment` admissibility fields. -/
theorem genuine_judgment_same_is_equality
    (J : TraceJudgment)
    (htight : ∀ (T : Trace) (a b : Endpoint), J.diff T a b ↔ ¬ J.same T a b)
    (hsep : ∀ T : Trace, J.diff T Endpoint.left Endpoint.right)
    (T : Trace) (a b : Endpoint) :
    J.same T a b ↔ a = b := by
  have hne : ¬ J.same T Endpoint.left Endpoint.right :=
    (htight T Endpoint.left Endpoint.right).mp (hsep T)
  constructor
  · intro hsame
    rcases endpoint_eq_left_or_right a with ha | ha <;>
      rcases endpoint_eq_left_or_right b with hb | hb <;>
      subst ha <;> subst hb
    · rfl
    · exact absurd hsame hne
    · exact absurd (J.same_symm T hsame) hne
    · rfl
  · intro hab
    subst hab
    exact J.same_refl T a

/-- **Item 5 resolution.** Recognition is one primitive. For any judgment that is
an equivalence (the admissibility fields), tight, and separating, the `same`
relation is forced to be the decidable equality carried by the act-generated
structure. Hence the same/different judgment is derived from the act, not an
independent second primitive. -/
theorem comparison_is_derived_not_primitive
    (J : TraceJudgment)
    (htight : ∀ (T : Trace) (a b : Endpoint), J.diff T a b ↔ ¬ J.same T a b)
    (hsep : ∀ T : Trace, J.diff T Endpoint.left Endpoint.right) :
    ∀ (T : Trace) (a b : Endpoint),
      (J.same T a b ↔ a = b)
        ∧ (J.same T a b ↔ actJudgment.same T a b) := by
  intro T a b
  have h := genuine_judgment_same_is_equality J htight hsep T a b
  exact ⟨h, h.trans (actJudgment_same T a b).symm⟩

end OnePrimitive
end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

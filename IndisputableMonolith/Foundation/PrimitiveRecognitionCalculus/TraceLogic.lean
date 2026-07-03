/-
  PrimitiveRecognitionCalculus/TraceLogic.lean

  Round-trip source:
    δ/PRC_Universal_Foundation_Execution_Plan_20260526.html

  Spec anchor:
    Build Order step 11: build logical connectives and quantifier surfaces from
    stable trace predicates.

  This first pass keeps the logic surface over finite PRC traces. Completed
  trace families and model-theoretic inevitability are separate later layers.
-/

import IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.SameDiff

namespace IndisputableMonolith
namespace Foundation
namespace PrimitiveRecognitionCalculus

/-- A proposition in the first PRC logic pass is a predicate on finite traces
that persists under trace extension. -/
structure TracePredicate where
  holds : Trace → Prop
  stable :
    ∀ {T U : Trace}, Trace.Extends T U → holds T → holds U

namespace TracePredicate

/-- Truth is the stable predicate that holds at every trace. -/
def top : TracePredicate where
  holds := fun _ => True
  stable := by
    intro _T _U _hTU _h
    trivial

/-- Falsehood is the stable predicate that holds at no trace. -/
def bottom : TracePredicate where
  holds := fun _ => False
  stable := by
    intro _T _U _hTU h
    exact False.elim h

/-- Conjunction of stable trace predicates. -/
def and (P Q : TracePredicate) : TracePredicate where
  holds := fun T => P.holds T ∧ Q.holds T
  stable := by
    intro T U hTU h
    exact ⟨P.stable hTU h.1, Q.stable hTU h.2⟩

/-- Disjunction of stable trace predicates. -/
def or (P Q : TracePredicate) : TracePredicate where
  holds := fun T => P.holds T ∨ Q.holds T
  stable := by
    intro T U hTU h
    cases h with
    | inl hP => exact Or.inl (P.stable hTU hP)
    | inr hQ => exact Or.inr (Q.stable hTU hQ)

/-- Implication is persistence along every future extension of the current
trace. This makes implication itself stable under extension. -/
def imp (P Q : TracePredicate) : TracePredicate where
  holds := fun T =>
    ∀ U : Trace, Trace.Extends T U → P.holds U → Q.holds U
  stable := by
    intro T U hTU h V hUV hPV
    exact h V (Trace.extends_trans hTU hUV) hPV

/-- Negation is implication into falsehood. -/
def not (P : TracePredicate) : TracePredicate :=
  imp P bottom

/-- Universal quantification over a verifier-indexed family of stable trace
predicates. The family parameter is verifier bookkeeping; stability is still a
finite-trace theorem. -/
def all {α : Type} (P : α → TracePredicate) : TracePredicate where
  holds := fun T => ∀ a : α, (P a).holds T
  stable := by
    intro T U hTU h a
    exact (P a).stable hTU (h a)

/-- Existential quantification over a verifier-indexed family of stable trace
predicates. The witness is preserved while the trace is extended. -/
def exists_ {α : Type} (P : α → TracePredicate) : TracePredicate where
  holds := fun T => ∃ a : α, (P a).holds T
  stable := by
    intro T U hTU h
    rcases h with ⟨a, ha⟩
    exact ⟨a, (P a).stable hTU ha⟩

theorem top_intro (T : Trace) :
    top.holds T := by
  trivial

theorem and_intro {P Q : TracePredicate} {T : Trace}
    (hP : P.holds T) (hQ : Q.holds T) :
    (and P Q).holds T := by
  exact ⟨hP, hQ⟩

theorem and_left {P Q : TracePredicate} {T : Trace}
    (h : (and P Q).holds T) :
    P.holds T := by
  exact h.1

theorem and_right {P Q : TracePredicate} {T : Trace}
    (h : (and P Q).holds T) :
    Q.holds T := by
  exact h.2

theorem or_inl {P Q : TracePredicate} {T : Trace}
    (hP : P.holds T) :
    (or P Q).holds T := by
  exact Or.inl hP

theorem or_inr {P Q : TracePredicate} {T : Trace}
    (hQ : Q.holds T) :
    (or P Q).holds T := by
  exact Or.inr hQ

theorem imp_elim {P Q : TracePredicate} {T U : Trace}
    (himp : (imp P Q).holds T)
    (hTU : Trace.Extends T U)
    (hP : P.holds U) :
    Q.holds U := by
  exact himp U hTU hP

theorem not_elim {P : TracePredicate} {T U : Trace}
    (hn : (not P).holds T)
    (hTU : Trace.Extends T U)
    (hP : P.holds U) :
    False := by
  exact hn U hTU hP

theorem all_intro {α : Type} {P : α → TracePredicate} {T : Trace}
    (h : ∀ a : α, (P a).holds T) :
    (all P).holds T := by
  exact h

theorem all_elim {α : Type} {P : α → TracePredicate} {T : Trace}
    (h : (all P).holds T) (a : α) :
    (P a).holds T := by
  exact h a

theorem exists_intro {α : Type} {P : α → TracePredicate} {T : Trace}
    (a : α) (h : (P a).holds T) :
    (exists_ P).holds T := by
  exact ⟨a, h⟩

theorem persists {P : TracePredicate} {T U : Trace}
    (hTU : Trace.Extends T U) (hP : P.holds T) :
    P.holds U :=
  P.stable hTU hP

end TracePredicate

/-- Headline target for the first trace-logic pass. -/
structure TraceLogicCertificate : Prop where
  proposition_surface : Nonempty TracePredicate
  truth_intro : ∀ T : Trace, TracePredicate.top.holds T
  conjunction_intro :
    ∀ {P Q : TracePredicate} {T : Trace},
      P.holds T → Q.holds T → (TracePredicate.and P Q).holds T
  conjunction_left :
    ∀ {P Q : TracePredicate} {T : Trace},
      (TracePredicate.and P Q).holds T → P.holds T
  conjunction_right :
    ∀ {P Q : TracePredicate} {T : Trace},
      (TracePredicate.and P Q).holds T → Q.holds T
  disjunction_left :
    ∀ {P Q : TracePredicate} {T : Trace},
      P.holds T → (TracePredicate.or P Q).holds T
  disjunction_right :
    ∀ {P Q : TracePredicate} {T : Trace},
      Q.holds T → (TracePredicate.or P Q).holds T
  implication_elim :
    ∀ {P Q : TracePredicate} {T U : Trace},
      (TracePredicate.imp P Q).holds T →
        Trace.Extends T U → P.holds U → Q.holds U
  negation_elim :
    ∀ {P : TracePredicate} {T U : Trace},
      (TracePredicate.not P).holds T →
        Trace.Extends T U → P.holds U → False
  universal_intro :
    ∀ {α : Type} {P : α → TracePredicate} {T : Trace},
      (∀ a : α, (P a).holds T) → (TracePredicate.all P).holds T
  universal_elim :
    ∀ {α : Type} {P : α → TracePredicate} {T : Trace},
      (TracePredicate.all P).holds T → ∀ a : α, (P a).holds T
  existential_intro :
    ∀ {α : Type} {P : α → TracePredicate} {T : Trace},
      ∀ a : α, (P a).holds T → (TracePredicate.exists_ P).holds T
  persistence :
    ∀ {P : TracePredicate} {T U : Trace},
      Trace.Extends T U → P.holds T → P.holds U
  strength_tag : StrengthTag.deltaOnly = StrengthTag.deltaOnly

theorem trace_logic_certificate : TraceLogicCertificate where
  proposition_surface := ⟨TracePredicate.top⟩
  truth_intro := TracePredicate.top_intro
  conjunction_intro := by
    intro P Q T hP hQ
    exact TracePredicate.and_intro hP hQ
  conjunction_left := by
    intro P Q T h
    exact TracePredicate.and_left h
  conjunction_right := by
    intro P Q T h
    exact TracePredicate.and_right h
  disjunction_left := by
    intro P Q T hP
    exact TracePredicate.or_inl hP
  disjunction_right := by
    intro P Q T hQ
    exact TracePredicate.or_inr hQ
  implication_elim := by
    intro P Q T U himp hTU hP
    exact TracePredicate.imp_elim himp hTU hP
  negation_elim := by
    intro P T U hn hTU hP
    exact TracePredicate.not_elim hn hTU hP
  universal_intro := by
    intro α P T h
    exact TracePredicate.all_intro h
  universal_elim := by
    intro α P T h a
    exact TracePredicate.all_elim h a
  existential_intro := by
    intro α P T a h
    exact TracePredicate.exists_intro a h
  persistence := by
    intro P T U hTU hP
    exact TracePredicate.persists hTU hP
  strength_tag := rfl

end PrimitiveRecognitionCalculus
end Foundation
end IndisputableMonolith

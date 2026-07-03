import IndisputableMonolith.DeltaKernel.Syntax
import IndisputableMonolith.DeltaKernel.Ledger

/-!
# δ-Kernel: Derivations and the Ledger-Auditing Checker

A derivation is DATA: a fully annotated natural-deduction tree for
intuitionistic Heyting arithmetic over the distinction signature. It is not
a term inhabiting a type; there are no types. The kernel is the total
function `check : Ctx → Deriv → Option (DFormula × Ledger)` which either
rejects the tree or returns the proved formula together with the exact set
of posits consumed.

Rule inventory:
- Structural: hypothesis by de Bruijn index into the context.
- Equality: reflexivity and Leibniz substitution (symmetry/transitivity
  are derivable).
- Distinction axioms (the free structure ℕδ): `S t ≠ 0`, injectivity of
  `S`, and the primitive-recursive defining equations of `+` and `·`
  (each licensed by initiality: "freeness is forcing").
- Induction: the initiality schema itself.
- Intuitionistic propositional and quantifier rules (complete ND set).
- Posit rules: EM, LPO, MP as first-order schemas. These are the ONLY rules
  that post to the ledger. MP is restricted to quantifier-free matrices
  (checked by `isQF`), keeping the posit honestly weaker than EM.

A `sorry` has no counterpart here: there is no rule that closes a goal
without a complete sub-tree, so an incomplete derivation is simply an
ill-formed tree and the checker rejects it.
-/

namespace IndisputableMonolith
namespace DeltaKernel

open DTerm DFormula

/-- Contexts: hypothesis `i` is the `i`-th formula (de Bruijn into the list). -/
abbrev Ctx := List DFormula

/-- Fully annotated natural-deduction derivations. Annotations are chosen so
that checking requires no unification and no search: every rule's conclusion
is computable from its annotations and its sub-conclusions. -/
inductive Deriv : Type where
  /-- Hypothesis: the `i`-th formula of the context. -/
  | hyp        : Nat → Deriv
  /-- `⊢ t = t`. -/
  | eqRefl     : DTerm → Deriv
  /-- Leibniz: from `t = s` and `φ[t/x₀]` conclude `φ[s/x₀]`.
  Annotations: the hole formula `φ`, the terms `t`, `s`. -/
  | eqSubst    : DFormula → DTerm → DTerm → Deriv → Deriv → Deriv
  /-- Distinction axiom: `⊢ ¬(S t = 0)`. A fresh distinction is not silence. -/
  | succNeZero : DTerm → Deriv
  /-- Distinction axiom: from `S t = S s` conclude `t = s` (injectivity). -/
  | succInj    : Deriv → Deriv
  /-- Recursion equation: `⊢ t + 0 = t`. -/
  | addZero    : DTerm → Deriv
  /-- Recursion equation: `⊢ t + S s = S (t + s)`. -/
  | addSucc    : DTerm → DTerm → Deriv
  /-- Recursion equation: `⊢ t · 0 = 0`. -/
  | mulZero    : DTerm → Deriv
  /-- Recursion equation: `⊢ t · S s = t · s + t`. -/
  | mulSucc    : DTerm → DTerm → Deriv
  /-- Induction (initiality of ℕδ): from `φ[0/x₀]` and
  `∀x (φ → φ[S x₀/x₀])` conclude `∀x φ`. Annotation: `φ`. -/
  | ind        : DFormula → Deriv → Deriv → Deriv
  /-- From a proof of `ψ` under extra hypothesis `φ`, conclude `φ → ψ`. -/
  | implIntro  : DFormula → Deriv → Deriv
  /-- Modus ponens. -/
  | implElim   : Deriv → Deriv → Deriv
  | conjIntro  : Deriv → Deriv → Deriv
  | conjElim1  : Deriv → Deriv
  | conjElim2  : Deriv → Deriv
  /-- From `φ` conclude `φ ∨ ψ` (annotation: `ψ`). -/
  | disjIntro1 : DFormula → Deriv → Deriv
  /-- From `ψ` conclude `φ ∨ ψ` (annotation: `φ`). -/
  | disjIntro2 : DFormula → Deriv → Deriv
  /-- Case split: from `φ ∨ ψ`, a proof of `χ` under `φ`, and a proof of
  `χ` under `ψ`, conclude `χ`. -/
  | disjElim   : Deriv → Deriv → Deriv → Deriv
  /-- Ex falso: from `⊥` conclude any annotated `φ`. -/
  | flsElim    : DFormula → Deriv → Deriv
  /-- Generalization: from a proof of `φ` in the lifted context conclude
  `∀ φ` (the fresh eigenvariable is de Bruijn 0). -/
  | allIntro   : Deriv → Deriv
  /-- Instantiation: from `∀ φ` conclude `φ[t/x₀]` (annotation: `t`). -/
  | allElim    : DTerm → Deriv → Deriv
  /-- Witness: from `φ[t/x₀]` conclude `∃ φ` (annotations: `φ`, `t`). -/
  | exIntro    : DFormula → DTerm → Deriv → Deriv
  /-- Use: from `∃ φ` and a proof of `ψ` (lifted) under `φ` in the lifted
  context, conclude `ψ` (annotation: `ψ`, which must not mention the
  eigenvariable; enforced by requiring the sub-proof to conclude
  `ψ` lifted). -/
  | exElim     : DFormula → Deriv → Deriv → Deriv
  /-- POSIT (EM): `⊢ φ ∨ ¬φ`. Posts `em`. -/
  | emPosit    : DFormula → Deriv
  /-- POSIT (LPO, arithmetical form):
  `⊢ (∀x (φ ∨ ¬φ)) → ((∃x φ) ∨ (∀x ¬φ))`. Posts `lpo`. -/
  | lpoPosit   : DFormula → Deriv
  /-- POSIT (MP): `⊢ ¬¬(∃x φ) → ∃x φ` for quantifier-free `φ`. Posts `mp`. -/
  | mpPosit    : DFormula → Deriv
deriving Repr

/-- The kernel: audit a derivation tree in a context. Returns the proved
formula and the exact posit ledger, or `none` if the tree is ill-formed.
Total, structural, and `Prop`-free: the object logic never touches the
host's propositions. -/
def check (Γ : Ctx) : Deriv → Option (DFormula × Ledger)
  | .hyp i =>
      match Γ[i]? with
      | some φ => some (φ, .empty)
      | none => none
  | .eqRefl t => some (.eq t t, .empty)
  | .eqSubst φ t s dEq dT =>
      match check Γ dEq, check Γ dT with
      | some (cEq, o₁), some (cT, o₂) =>
          if cEq = DFormula.eq t s then
            if cT = φ.subst 0 t then some (φ.subst 0 s, o₁.union o₂)
            else none
          else none
      | _, _ => none
  | .succNeZero t => some (.neg (.eq (.succ t) .zero), .empty)
  | .succInj d =>
      match check Γ d with
      | some (.eq (.succ t) (.succ s), o) => some (.eq t s, o)
      | _ => none
  | .addZero t => some (.eq (.add t .zero) t, .empty)
  | .addSucc t s => some (.eq (.add t (.succ s)) (.succ (.add t s)), .empty)
  | .mulZero t => some (.eq (.mul t .zero) .zero, .empty)
  | .mulSucc t s => some (.eq (.mul t (.succ s)) (.add (.mul t s) t), .empty)
  | .ind φ d₀ dS =>
      match check Γ d₀, check Γ dS with
      | some (c₀, o₁), some (cS, o₂) =>
          if c₀ = φ.subst 0 .zero then
            if cS = DFormula.all (.impl φ φ.stepSucc) then
              -- Stratification: induction on a quantified formula posts the
              -- FULL-IND tier flag; on a QF formula it stays in the QF tier.
              -- Whether FULL-IND is "forced by initiality" or a strength step
              -- is the measured question the flag exists to answer.
              let base := o₁.union o₂
              let o := if φ.isQF then base else base.union .ofIndFull
              some (.all φ, o)
            else none
          else none
      | _, _ => none
  | .implIntro φ d =>
      match check (φ :: Γ) d with
      | some (ψ, o) => some (.impl φ ψ, o)
      | none => none
  | .implElim d₁ d₂ =>
      match check Γ d₁, check Γ d₂ with
      | some (.impl φ ψ, o₁), some (φ', o₂) =>
          if φ' = φ then some (ψ, o₁.union o₂) else none
      | _, _ => none
  | .conjIntro d₁ d₂ =>
      match check Γ d₁, check Γ d₂ with
      | some (φ, o₁), some (ψ, o₂) => some (.conj φ ψ, o₁.union o₂)
      | _, _ => none
  | .conjElim1 d =>
      match check Γ d with
      | some (.conj φ _, o) => some (φ, o)
      | _ => none
  | .conjElim2 d =>
      match check Γ d with
      | some (.conj _ ψ, o) => some (ψ, o)
      | _ => none
  | .disjIntro1 ψ d =>
      match check Γ d with
      | some (φ, o) => some (.disj φ ψ, o)
      | none => none
  | .disjIntro2 φ d =>
      match check Γ d with
      | some (ψ, o) => some (.disj φ ψ, o)
      | none => none
  | .disjElim d dL dR =>
      match check Γ d with
      | some (.disj φ ψ, o) =>
          match check (φ :: Γ) dL, check (ψ :: Γ) dR with
          | some (χ₁, o₁), some (χ₂, o₂) =>
              if χ₁ = χ₂ then some (χ₁, (o.union o₁).union o₂) else none
          | _, _ => none
      | _ => none
  | .flsElim φ d =>
      match check Γ d with
      | some (.fls, o) => some (φ, o)
      | _ => none
  | .allIntro d =>
      match check (Γ.map (DFormula.lift 1 0)) d with
      | some (φ, o) => some (.all φ, o)
      | none => none
  | .allElim t d =>
      match check Γ d with
      | some (.all φ, o) => some (φ.subst 0 t, o)
      | _ => none
  | .exIntro φ t d =>
      match check Γ d with
      | some (c, o) =>
          if c = φ.subst 0 t then some (.ex φ, o) else none
      | none => none
  | .exElim ψ d dBody =>
      match check Γ d with
      | some (.ex φ, o) =>
          match check (φ :: Γ.map (DFormula.lift 1 0)) dBody with
          | some (ψ', o₂) =>
              if ψ' = ψ.lift 1 0 then some (ψ, o.union o₂) else none
          | none => none
      | _ => none
  | .emPosit φ => some (.disj φ φ.neg, .ofEM)
  | .lpoPosit φ =>
      some (.impl (.all (.disj φ φ.neg)) (.disj (.ex φ) (.all φ.neg)), .ofLPO)
  | .mpPosit φ =>
      if φ.isQF then some (.impl (.neg (.neg (.ex φ))) (.ex φ), .ofMP)
      else none

/-- FORCED verdict: the tree checks with an empty ledger. This is the
kernel-native σ0 / DELTA_FORCED certificate. -/
def Forced (Γ : Ctx) (d : Deriv) (φ : DFormula) : Prop :=
  check Γ d = some (φ, Ledger.empty)

/-- CONDITIONAL verdict: the tree checks, and the ledger names its posits. -/
def Conditional (Γ : Ctx) (d : Deriv) (φ : DFormula) (O : Ledger) : Prop :=
  check Γ d = some (φ, O)

end DeltaKernel
end IndisputableMonolith

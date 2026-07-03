import IndisputableMonolith.DeltaKernel.Check

/-!
# δ-Kernel: The Syntactic σ-Scan (Oracle-Symbol Tamper Evidence)

The panel's oracle-symbol refactor, realized without changing the derivation
language: the posits ARE syntactic symbols already, because a derivation is
plain data and the only constructors that can post to the ledger are the three
posit nodes (`emPosit`, `lpoPosit`, `mpPosit`) and the induction node on a
quantified formula. So the σ-grade of a derivation is computable by a fold
over the tree that never consults the checker, the context, or any semantic
notion, exactly the way one would grep a Lean proof term for
`Classical.choice`.

This module provides that fold (`scanLedger`), the two grep-level Boolean
scans (`positFree`, `usesFullInd`), and the AGREEMENT THEOREM: on every
derivation the checker accepts, the checker's threaded ledger EQUALS the
syntactic scan. Consequences:

- The ledger cannot be forged by routing: no arrangement of the forced rules
  can synthesize a posit flag, and no arrangement of posits can hide one
  (`scan_eq_check` + `Ledger.union_isForced`).
- A FORCED verdict is equivalent to the syntactic ABSENCE of posit symbols in
  the tree (`forced_iff_positFree`), so a third party can audit a σ0 claim
  with a tree-walk, independent of the kernel implementation.
- The induction TIER is likewise a syntactic occurrence check
  (`usesFullInd_eq_scan_indFull`): `FORCED @ QF-IND` is grep-auditable.

Everything here is choice-free structural recursion. No Mathlib.
-/

namespace IndisputableMonolith
namespace DeltaKernel

/-- The syntactic σ-scan: compute the ledger by folding over the derivation
TREE, ignoring contexts and conclusions entirely. Posit constructors
contribute their posit; an induction node on a quantified formula contributes
the FULL-IND tier flag; everything else merges its children. -/
def scanLedger : Deriv → Ledger
  | .hyp _ => .empty
  | .eqRefl _ => .empty
  | .eqSubst _ _ _ dEq dT => (scanLedger dEq).union (scanLedger dT)
  | .succNeZero _ => .empty
  | .succInj d => scanLedger d
  | .addZero _ => .empty
  | .addSucc _ _ => .empty
  | .mulZero _ => .empty
  | .mulSucc _ _ => .empty
  | .ind φ d₀ dS =>
      if φ.isQF then (scanLedger d₀).union (scanLedger dS)
      else ((scanLedger d₀).union (scanLedger dS)).union .ofIndFull
  | .implIntro _ d => scanLedger d
  | .implElim d₁ d₂ => (scanLedger d₁).union (scanLedger d₂)
  | .conjIntro d₁ d₂ => (scanLedger d₁).union (scanLedger d₂)
  | .conjElim1 d => scanLedger d
  | .conjElim2 d => scanLedger d
  | .disjIntro1 _ d => scanLedger d
  | .disjIntro2 _ d => scanLedger d
  | .disjElim d dL dR => ((scanLedger d).union (scanLedger dL)).union (scanLedger dR)
  | .flsElim _ d => scanLedger d
  | .allIntro d => scanLedger d
  | .allElim _ d => scanLedger d
  | .exIntro _ _ d => scanLedger d
  | .exElim _ d dBody => (scanLedger d).union (scanLedger dBody)
  | .emPosit _ => .ofEM
  | .lpoPosit _ => .ofLPO
  | .mpPosit _ => .ofMP

/-- Grep-level scan: the tree contains NO posit constructor. This is the
oracle-symbol audit a third party can run without knowing anything about the
checker: walk the tree, look for the three posit symbols. -/
def positFree : Deriv → Bool
  | .hyp _ => true
  | .eqRefl _ => true
  | .eqSubst _ _ _ dEq dT => positFree dEq && positFree dT
  | .succNeZero _ => true
  | .succInj d => positFree d
  | .addZero _ => true
  | .addSucc _ _ => true
  | .mulZero _ => true
  | .mulSucc _ _ => true
  | .ind _ d₀ dS => positFree d₀ && positFree dS
  | .implIntro _ d => positFree d
  | .implElim d₁ d₂ => positFree d₁ && positFree d₂
  | .conjIntro d₁ d₂ => positFree d₁ && positFree d₂
  | .conjElim1 d => positFree d
  | .conjElim2 d => positFree d
  | .disjIntro1 _ d => positFree d
  | .disjIntro2 _ d => positFree d
  | .disjElim d dL dR => (positFree d && positFree dL) && positFree dR
  | .flsElim _ d => positFree d
  | .allIntro d => positFree d
  | .allElim _ d => positFree d
  | .exIntro _ _ d => positFree d
  | .exElim _ d dBody => positFree d && positFree dBody
  | .emPosit _ => false
  | .lpoPosit _ => false
  | .mpPosit _ => false

/-- Grep-level scan: the tree contains an induction node whose formula has
quantifiers (the FULL-IND tier symbol). -/
def usesFullInd : Deriv → Bool
  | .hyp _ => false
  | .eqRefl _ => false
  | .eqSubst _ _ _ dEq dT => usesFullInd dEq || usesFullInd dT
  | .succNeZero _ => false
  | .succInj d => usesFullInd d
  | .addZero _ => false
  | .addSucc _ _ => false
  | .mulZero _ => false
  | .mulSucc _ _ => false
  | .ind φ d₀ dS => ((!φ.isQF) || usesFullInd d₀) || usesFullInd dS
  | .implIntro _ d => usesFullInd d
  | .implElim d₁ d₂ => usesFullInd d₁ || usesFullInd d₂
  | .conjIntro d₁ d₂ => usesFullInd d₁ || usesFullInd d₂
  | .conjElim1 d => usesFullInd d
  | .conjElim2 d => usesFullInd d
  | .disjIntro1 _ d => usesFullInd d
  | .disjIntro2 _ d => usesFullInd d
  | .disjElim d dL dR => (usesFullInd d || usesFullInd dL) || usesFullInd dR
  | .flsElim _ d => usesFullInd d
  | .allIntro d => usesFullInd d
  | .allElim _ d => usesFullInd d
  | .exIntro _ _ d => usesFullInd d
  | .exElim _ d dBody => usesFullInd d || usesFullInd dBody
  | .emPosit _ => false
  | .lpoPosit _ => false
  | .mpPosit _ => false

/-! ## The scans are faithful to the ledger algebra -/

/-- The grep scan for posits agrees with `isForced` of the syntactic ledger:
a tree is posit-free iff its scanned ledger is FORCED. -/
theorem positFree_eq_scan_isForced (d : Deriv) :
    positFree d = (scanLedger d).isForced := by
  induction d with
  | hyp _ => rfl
  | eqRefl _ => rfl
  | eqSubst _ _ _ dEq dT ihE ihT =>
      simp [positFree, scanLedger, Ledger.union_isForced, ihE, ihT]
  | succNeZero _ => rfl
  | succInj d ih => simpa [positFree, scanLedger] using ih
  | addZero _ => rfl
  | addSucc _ _ => rfl
  | mulZero _ => rfl
  | mulSucc _ _ => rfl
  | ind φ d₀ dS ih₀ ihS =>
      cases hqf : φ.isQF <;>
        simp [positFree, scanLedger, hqf, Ledger.union_isForced,
          Ledger.ofIndFull_isForced, ih₀, ihS]
  | implIntro _ d ih => simpa [positFree, scanLedger] using ih
  | implElim d₁ d₂ ih₁ ih₂ =>
      simp [positFree, scanLedger, Ledger.union_isForced, ih₁, ih₂]
  | conjIntro d₁ d₂ ih₁ ih₂ =>
      simp [positFree, scanLedger, Ledger.union_isForced, ih₁, ih₂]
  | conjElim1 d ih => simpa [positFree, scanLedger] using ih
  | conjElim2 d ih => simpa [positFree, scanLedger] using ih
  | disjIntro1 _ d ih => simpa [positFree, scanLedger] using ih
  | disjIntro2 _ d ih => simpa [positFree, scanLedger] using ih
  | disjElim d dL dR ih ihL ihR =>
      simp [positFree, scanLedger, Ledger.union_isForced, ih, ihL, ihR]
  | flsElim _ d ih => simpa [positFree, scanLedger] using ih
  | allIntro d ih => simpa [positFree, scanLedger] using ih
  | allElim _ d ih => simpa [positFree, scanLedger] using ih
  | exIntro _ _ d ih => simpa [positFree, scanLedger] using ih
  | exElim _ d dBody ih ihB =>
      simp [positFree, scanLedger, Ledger.union_isForced, ih, ihB]
  | emPosit _ => rfl
  | lpoPosit _ => rfl
  | mpPosit _ => rfl

/-- The grep scan for the induction tier agrees with the `indFull` flag of the
syntactic ledger. -/
theorem usesFullInd_eq_scan_indFull (d : Deriv) :
    usesFullInd d = (scanLedger d).indFull := by
  induction d with
  | hyp _ => rfl
  | eqRefl _ => rfl
  | eqSubst _ _ _ dEq dT ihE ihT =>
      simp [usesFullInd, scanLedger, Ledger.union, ihE, ihT]
  | succNeZero _ => rfl
  | succInj d ih => simpa [usesFullInd, scanLedger] using ih
  | addZero _ => rfl
  | addSucc _ _ => rfl
  | mulZero _ => rfl
  | mulSucc _ _ => rfl
  | ind φ d₀ dS ih₀ ihS =>
      cases hqf : φ.isQF <;>
        simp [usesFullInd, scanLedger, hqf, Ledger.union, Ledger.ofIndFull,
          ih₀, ihS]
  | implIntro _ d ih => simpa [usesFullInd, scanLedger] using ih
  | implElim d₁ d₂ ih₁ ih₂ =>
      simp [usesFullInd, scanLedger, Ledger.union, ih₁, ih₂]
  | conjIntro d₁ d₂ ih₁ ih₂ =>
      simp [usesFullInd, scanLedger, Ledger.union, ih₁, ih₂]
  | conjElim1 d ih => simpa [usesFullInd, scanLedger] using ih
  | conjElim2 d ih => simpa [usesFullInd, scanLedger] using ih
  | disjIntro1 _ d ih => simpa [usesFullInd, scanLedger] using ih
  | disjIntro2 _ d ih => simpa [usesFullInd, scanLedger] using ih
  | disjElim d dL dR ih ihL ihR =>
      simp [usesFullInd, scanLedger, Ledger.union, ih, ihL, ihR]
  | flsElim _ d ih => simpa [usesFullInd, scanLedger] using ih
  | allIntro d ih => simpa [usesFullInd, scanLedger] using ih
  | allElim _ d ih => simpa [usesFullInd, scanLedger] using ih
  | exIntro _ _ d ih => simpa [usesFullInd, scanLedger] using ih
  | exElim _ d dBody ih ihB =>
      simp [usesFullInd, scanLedger, Ledger.union, ih, ihB]
  | emPosit _ => rfl
  | lpoPosit _ => rfl
  | mpPosit _ => rfl

/-! ## The agreement theorem: checker ledger = syntactic scan -/

/-- AGREEMENT: on every derivation the checker accepts, the checker's
threaded ledger is EXACTLY the syntactic σ-scan of the tree. So the σ-grade
of a checked judgment is an oracle-symbol occurrence fact about the
derivation data, not an artifact of the checking algorithm: the ledger is
tamper-evident. -/
theorem scan_eq_check {d : Deriv} :
    ∀ {Γ : Ctx} {φ : DFormula} {O : Ledger},
      check Γ d = some (φ, O) → O = scanLedger d := by
  induction d with
  | hyp i =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hg : Γ[i]? with
      | none => simp [hg] at hchk
      | some ψ =>
          simp only [hg, Option.some.injEq, Prod.mk.injEq] at hchk
          exact hchk.2.symm
  | eqRefl t =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | eqSubst hole t s dEq dT ihEq ihT =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hdE : check Γ dEq with
      | none => simp [hdE] at hchk
      | some cpE =>
          obtain ⟨cEq, o₁⟩ := cpE
          cases hdT : check Γ dT with
          | none => simp [hdE, hdT] at hchk
          | some cpT =>
              obtain ⟨cT, o₂⟩ := cpT
              simp only [hdE, hdT] at hchk
              split at hchk
              · split at hchk
                · simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                  obtain ⟨_, hO⟩ := hchk
                  rw [ihEq hdE, ihT hdT] at hO
                  exact hO.symm
                · nomatch hchk
              · nomatch hchk
  | succNeZero t =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | succInj d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | eq a b =>
              cases a with
              | succ ta =>
                  cases b with
                  | succ tb =>
                      simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
                      obtain ⟨_, hO⟩ := hchk
                      rw [ih hd] at hO
                      exact hO.symm
                  | var _ => simp [hd] at hchk
                  | zero => simp [hd] at hchk
                  | add _ _ => simp [hd] at hchk
                  | mul _ _ => simp [hd] at hchk
              | var _ => simp [hd] at hchk
              | zero => simp [hd] at hchk
              | add _ _ => simp [hd] at hchk
              | mul _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | addZero t =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | addSucc t s =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | mulZero t =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | mulSucc t s =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | ind hole d₀ dS ih₀ ihS =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd0 : check Γ d₀ with
      | none => simp [hd0] at hchk
      | some cp0 =>
          obtain ⟨c₀, o₁⟩ := cp0
          cases hdS : check Γ dS with
          | none => simp [hd0, hdS] at hchk
          | some cpS =>
              obtain ⟨cS, o₂⟩ := cpS
              simp only [hd0, hdS] at hchk
              split at hchk
              · split at hchk
                · simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                  obtain ⟨_, hO⟩ := hchk
                  rw [ih₀ hd0, ihS hdS] at hO
                  exact hO.symm
                · nomatch hchk
              · nomatch hchk
  | implIntro hole d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check (hole :: Γ) d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨_, hO⟩ := hchk
          rw [ih hd] at hO
          exact hO.symm
  | implElim d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd1 : check Γ d₁ with
      | none => simp [hd1] at hchk
      | some cp1 =>
          obtain ⟨c₁, o₁⟩ := cp1
          cases hd2 : check Γ d₂ with
          | none => simp [hd1, hd2] at hchk
          | some cp2 =>
              obtain ⟨c₂, o₂⟩ := cp2
              cases c₁ with
              | impl a b =>
                  simp only [hd1, hd2] at hchk
                  split at hchk
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                    obtain ⟨_, hO⟩ := hchk
                    rw [ih₁ hd1, ih₂ hd2] at hO
                    exact hO.symm
                  · nomatch hchk
              | eq _ _ => simp [hd1, hd2] at hchk
              | fls => simp [hd1, hd2] at hchk
              | conj _ _ => simp [hd1, hd2] at hchk
              | disj _ _ => simp [hd1, hd2] at hchk
              | all _ => simp [hd1, hd2] at hchk
              | ex _ => simp [hd1, hd2] at hchk
  | conjIntro d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd1 : check Γ d₁ with
      | none => simp [hd1] at hchk
      | some cp1 =>
          obtain ⟨c₁, o₁⟩ := cp1
          cases hd2 : check Γ d₂ with
          | none => simp [hd1, hd2] at hchk
          | some cp2 =>
              obtain ⟨c₂, o₂⟩ := cp2
              simp only [hd1, hd2, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨_, hO⟩ := hchk
              rw [ih₁ hd1, ih₂ hd2] at hO
              exact hO.symm
  | conjElim1 d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | conj a b =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨_, hO⟩ := hchk
              rw [ih hd] at hO
              exact hO.symm
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | conjElim2 d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | conj a b =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨_, hO⟩ := hchk
              rw [ih hd] at hO
              exact hO.symm
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | disjIntro1 ψ d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨_, hO⟩ := hchk
          rw [ih hd] at hO
          exact hO.symm
  | disjIntro2 ψ d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨_, hO⟩ := hchk
          rw [ih hd] at hO
          exact hO.symm
  | disjElim d dL dR ih ihL ihR =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | disj a b =>
              simp only [hd] at hchk
              cases hdL : check (a :: Γ) dL with
              | none => simp [hdL] at hchk
              | some cpL =>
                  obtain ⟨χ₁, o₁⟩ := cpL
                  cases hdR : check (b :: Γ) dR with
                  | none => simp [hdL, hdR] at hchk
                  | some cpR =>
                      obtain ⟨χ₂, o₂⟩ := cpR
                      simp only [hdL, hdR] at hchk
                      split at hchk
                      · simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                        obtain ⟨_, hO⟩ := hchk
                        rw [ih hd, ihL hdL, ihR hdR] at hO
                        exact hO.symm
                      · nomatch hchk
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | flsElim ψ d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | fls =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨_, hO⟩ := hchk
              rw [ih hd] at hO
              exact hO.symm
          | eq _ _ => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | allIntro d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check (Γ.map (DFormula.lift 1 0)) d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
          obtain ⟨_, hO⟩ := hchk
          rw [ih hd] at hO
          exact hO.symm
  | allElim t d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | all a =>
              simp only [hd, Option.some.injEq, Prod.mk.injEq] at hchk
              obtain ⟨_, hO⟩ := hchk
              rw [ih hd] at hO
              exact hO.symm
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | ex _ => simp [hd] at hchk
  | exIntro ψ t d ih =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          simp only [hd] at hchk
          split at hchk
          · simp only [Option.some.injEq, Prod.mk.injEq] at hchk
            obtain ⟨_, hO⟩ := hchk
            rw [ih hd] at hO
            exact hO.symm
          · nomatch hchk
  | exElim ψ d dBody ih ihBody =>
      intro Γ φ O hchk
      simp only [check] at hchk
      cases hd : check Γ d with
      | none => simp [hd] at hchk
      | some cp =>
          obtain ⟨c, o⟩ := cp
          cases c with
          | ex a =>
              simp only [hd] at hchk
              cases hdB : check (a :: Γ.map (DFormula.lift 1 0)) dBody with
              | none => simp [hdB] at hchk
              | some cpB =>
                  obtain ⟨χ, o₂⟩ := cpB
                  simp only [hdB] at hchk
                  split at hchk
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hchk
                    obtain ⟨_, hO⟩ := hchk
                    rw [ih hd, ihBody hdB] at hO
                    exact hO.symm
                  · nomatch hchk
          | eq _ _ => simp [hd] at hchk
          | fls => simp [hd] at hchk
          | conj _ _ => simp [hd] at hchk
          | disj _ _ => simp [hd] at hchk
          | impl _ _ => simp [hd] at hchk
          | all _ => simp [hd] at hchk
  | emPosit ψ =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | lpoPosit ψ =>
      intro Γ φ O hchk
      simp only [check, Option.some.injEq, Prod.mk.injEq] at hchk
      exact hchk.2.symm
  | mpPosit ψ =>
      intro Γ φ O hchk
      simp only [check] at hchk
      split at hchk
      · simp only [Option.some.injEq, Prod.mk.injEq] at hchk
        exact hchk.2.symm
      · nomatch hchk

/-! ## Corollaries: FORCED is a syntactic occurrence fact -/

/-- A checked derivation is FORCED iff its tree contains NO posit symbol.
Left to right is the tamper-evidence direction: a σ0 certificate implies the
grep-level audit passes. Right to left says the checker never invents posits. -/
theorem forced_iff_positFree {Γ : Ctx} {d : Deriv} {φ : DFormula} {O : Ledger}
    (h : check Γ d = some (φ, O)) :
    O.isForced = true ↔ positFree d = true := by
  rw [scan_eq_check h, positFree_eq_scan_isForced]

/-- A FORCED verdict (empty ledger) implies the tree is posit-free AND stayed
in the QF induction tier: the `σ0 @ QF-IND` certificate is a pure syntactic
occurrence fact, auditable by tree-walk with no knowledge of the checker. -/
theorem forced_syntactic_audit {Γ : Ctx} {d : Deriv} {φ : DFormula}
    (h : Forced Γ d φ) :
    positFree d = true ∧ usesFullInd d = false := by
  have hscan : Ledger.empty = scanLedger d := scan_eq_check h
  constructor
  · rw [positFree_eq_scan_isForced, ← hscan]; rfl
  · rw [usesFullInd_eq_scan_indFull, ← hscan]; rfl

/-- The checker's ledger on any accepted derivation is computable without
running the checker: `Conditional` σ-grades are grep-auditable too. -/
theorem conditional_ledger_syntactic {Γ : Ctx} {d : Deriv} {φ : DFormula}
    {O : Ledger} (h : Conditional Γ d φ O) : O = scanLedger d :=
  scan_eq_check h

end DeltaKernel
end IndisputableMonolith

/-!
# δ-Kernel: The Posit Ledger

The forcing-spectrum accounting made kernel-native. Every judgment of the
δ-kernel is `Γ ⊢_O φ` where `O` records (a) the named posits (omniscience /
classical principles) the derivation consumed and (b) the induction TIER it
used. The base rules of the forced fragment post nothing; each posit rule
posts its name; the induction rule posts the tier flag when the induction
formula has quantifiers.

Kernel verdicts:
- `FORCED`      : no posits consumed (σ0 in the forcing-spectrum sense),
- `CONDITIONAL` : posits nonempty; the posits are the σ-grade.

Stratification (panel-greenlit, 2026-07-02): whether FULL induction (over
quantified formulas) is forced by initiality or is itself a graded strength
step is a MEASURED question, not a pre-judged one. So the ledger carries an
`indFull` TIER flag separate from the posit alphabet: `isForced` looks only
at posits; the tier is reported alongside (`FORCED @ QF-IND` vs
`FORCED @ FULL-IND`). Reading the tier flag of the kernel's own soundness
derivation is the pre-registered self-grounding experiment.

The v0 posit alphabet is the paper's arithmetical fragment: EM (full excluded
middle schema), LPO (the limited principle of omniscience, arithmetical form),
MP (Markov's principle, quantifier-free matrices). The ledger is a record of
Booleans so that `union` and "empty ledger means every sub-ledger is empty"
are decidable structural facts, not list bookkeeping.
-/

namespace IndisputableMonolith
namespace DeltaKernel

/-- The posit-and-tier ledger. Fields `em`, `lpo`, `mp` are POSITS (named
classical/omniscience principles consumed). Field `indFull` is a TIER marker:
the derivation used induction on a formula with quantifiers. Extending the
posit alphabet = adding a field. -/
structure Ledger where
  /-- Full excluded middle schema `φ ∨ ¬φ`. -/
  em : Bool
  /-- Limited principle of omniscience (arithmetical form):
  pointwise decidability of `φ` yields `(∃x φ) ∨ (∀x ¬φ)`. -/
  lpo : Bool
  /-- Markov's principle for quantifier-free matrices:
  `¬¬(∃x φ) → ∃x φ`. -/
  mp : Bool
  /-- TIER (not a posit): induction was used on a non-quantifier-free
  formula. `FORCED @ FULL-IND` vs `FORCED @ QF-IND`. -/
  indFull : Bool
deriving Repr, DecidableEq

namespace Ledger

/-- The empty ledger: nothing posited, QF-induction tier. -/
def empty : Ledger := ⟨false, false, false, false⟩

/-- Merge two ledgers (a derivation consumes the posits of all its parts). -/
def union (a b : Ledger) : Ledger :=
  ⟨a.em || b.em, a.lpo || b.lpo, a.mp || b.mp, a.indFull || b.indFull⟩

/-- FORCED = no posits consumed. This looks only at the posit alphabet;
the induction tier is orthogonal (see `tierQF`). -/
def isForced (l : Ledger) : Bool := !l.em && !l.lpo && !l.mp

/-- The derivation stayed in the quantifier-free induction tier. -/
def tierQF (l : Ledger) : Bool := !l.indFull

/-- Ledger that posts only EM. -/
def ofEM : Ledger := ⟨true, false, false, false⟩

/-- Ledger that posts only LPO. -/
def ofLPO : Ledger := ⟨false, true, false, false⟩

/-- Ledger that posts only MP. -/
def ofMP : Ledger := ⟨false, false, true, false⟩

/-- Ledger that marks only the full-induction tier. -/
def ofIndFull : Ledger := ⟨false, false, false, true⟩

@[simp] theorem union_empty (a : Ledger) : a.union empty = a := by
  cases a; simp [union, empty]

@[simp] theorem empty_union (a : Ledger) : empty.union a = a := by
  cases a; simp [union, empty]

/-- A union is empty iff both parts are: the FORCED verdict is inherited by
every sub-derivation. -/
theorem union_eq_empty {a b : Ledger} :
    a.union b = empty ↔ a = empty ∧ b = empty := by
  cases a; cases b
  simp only [union, empty, Ledger.mk.injEq, Bool.or_eq_false_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩
    exact ⟨⟨h1, h3, h5, h7⟩, ⟨h2, h4, h6, h8⟩⟩
  · rintro ⟨⟨h1, h3, h5, h7⟩, ⟨h2, h4, h6, h8⟩⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩⟩

theorem ofEM_ne_empty : ofEM ≠ empty := by decide

theorem ofLPO_ne_empty : ofLPO ≠ empty := by decide

theorem ofMP_ne_empty : ofMP ≠ empty := by decide

/-! Posit-flag monotonicity under `union`: a posit consumed by either premise
is consumed by the combined judgment. These lemmas let the conditional
soundness proof thread per-posit semantic hypotheses down to sub-derivations. -/

theorem em_left {a b : Ledger} (h : a.em = true) : (a.union b).em = true := by
  simp [union, h]

theorem em_right {a b : Ledger} (h : b.em = true) : (a.union b).em = true := by
  simp [union, h]

theorem lpo_left {a b : Ledger} (h : a.lpo = true) : (a.union b).lpo = true := by
  simp [union, h]

theorem lpo_right {a b : Ledger} (h : b.lpo = true) : (a.union b).lpo = true := by
  simp [union, h]

theorem mp_left {a b : Ledger} (h : a.mp = true) : (a.union b).mp = true := by
  simp [union, h]

theorem mp_right {a b : Ledger} (h : b.mp = true) : (a.union b).mp = true := by
  simp [union, h]

/-! `isForced` as a union homomorphism, plus the posit-constant evaluations.
These are what let the checker-independent syntactic σ-scan (`Sigma.lean`)
agree with the checker's threaded ledger: FORCED distributes over `union` and
is orthogonal to the induction tier (`ofIndFull` is forced). -/

@[simp] theorem empty_isForced : empty.isForced = true := rfl

@[simp] theorem ofEM_isForced : ofEM.isForced = false := rfl

@[simp] theorem ofLPO_isForced : ofLPO.isForced = false := rfl

@[simp] theorem ofMP_isForced : ofMP.isForced = false := rfl

/-- The induction TIER is orthogonal to the posit alphabet: the full-induction
marker is still FORCED (no omniscience posited). This is why the σ-scan reads
`FORCED @ FULL-IND`, not `CONDITIONAL`, on a quantified induction. -/
@[simp] theorem ofIndFull_isForced : ofIndFull.isForced = true := rfl

/-- FORCED is a monoid homomorphism from `(union, empty)` to `(&&, true)`:
a merged judgment is forced iff both parts are. The De Morgan core of the
tamper-evidence proof. -/
theorem union_isForced (a b : Ledger) :
    (a.union b).isForced = (a.isForced && b.isForced) := by
  cases a with
  | mk e1 l1 m1 i1 =>
    cases b with
    | mk e2 l2 m2 i2 =>
      simp only [union, isForced]
      cases e1 <;> cases l1 <;> cases m1 <;> cases e2 <;> cases l2 <;> cases m2 <;> rfl

end Ledger

end DeltaKernel
end IndisputableMonolith

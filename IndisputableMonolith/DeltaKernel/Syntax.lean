/-!
# δ-Kernel: Syntax

Terms and formulas of the δ object logic: intuitionistic first-order
arithmetic over the distinction signature `{0, S, +, ·}`.

This is the syntax of the FORCED BASE of the δ framework
(`Delta_Forcing_Spectrum_20260626.tex`): the free distinction structure ℕδ
with its recursion-licensed operations. There is deliberately NO universe
hierarchy, NO Π-types, NO inductive-type scheme, NO propositions-as-types,
NO membership or comprehension. The object logic never touches the host's
`Prop`: formulas are plain data, and derivations (see `Check.lean`) are
plain data checked by a total function.

Variables are de Bruijn indices. `lift` and `subst` are the standard
binder-aware operations; both are structural recursion (σ0: no choice,
no classical logic, nothing beyond primitive-recursive syntax
manipulation).

This module imports nothing beyond the Lean prelude. No Mathlib.
-/

namespace IndisputableMonolith
namespace DeltaKernel

/-- Terms over the distinction signature: de Bruijn variables, zero,
successor (the distinction step), addition, multiplication.
`0` and `S` are the primitive signature of the free distinction structure;
`+` and `·` are the canonical recursion-licensed extensions (their defining
equations are axiom rules in `Check.lean`, licensed by initiality:
"freeness is forcing"). -/
inductive DTerm : Type where
  | var  : Nat → DTerm
  | zero : DTerm
  | succ : DTerm → DTerm
  | add  : DTerm → DTerm → DTerm
  | mul  : DTerm → DTerm → DTerm
deriving Repr, DecidableEq

namespace DTerm

/-- Shift the free variables `≥ c` up by `d`. -/
def lift (d c : Nat) : DTerm → DTerm
  | var n   => if n < c then var n else var (n + d)
  | zero    => zero
  | succ t  => succ (t.lift d c)
  | add t s => add (t.lift d c) (s.lift d c)
  | mul t s => mul (t.lift d c) (s.lift d c)

/-- Substitute `s` for variable `k` (binder instantiation: free variables
above `k` shift down by one). -/
def subst (k : Nat) (s : DTerm) : DTerm → DTerm
  | var n   => if n = k then s else if k < n then var (n - 1) else var n
  | zero    => zero
  | succ t  => succ (subst k s t)
  | add t u => add (subst k s t) (subst k s u)
  | mul t u => mul (subst k s t) (subst k s u)

/-- Numerals: the canonical image of the metatheoretic naturals. -/
def ofNat : Nat → DTerm
  | 0     => zero
  | n + 1 => succ (ofNat n)

end DTerm

/-- Formulas of intuitionistic first-order arithmetic over the distinction
signature. Equality is the sole atomic predicate (identity of ledger
content). Negation is defined: `¬φ := φ → ⊥`. -/
inductive DFormula : Type where
  | eq   : DTerm → DTerm → DFormula
  | fls  : DFormula
  | conj : DFormula → DFormula → DFormula
  | disj : DFormula → DFormula → DFormula
  | impl : DFormula → DFormula → DFormula
  | all  : DFormula → DFormula
  | ex   : DFormula → DFormula
deriving Repr, DecidableEq

namespace DFormula

/-- Negation, defined intuitionistically. -/
def neg (φ : DFormula) : DFormula := impl φ fls

/-- Shift the free variables `≥ c` up by `d` (binder-aware). -/
def lift (d c : Nat) : DFormula → DFormula
  | eq t s   => eq (t.lift d c) (s.lift d c)
  | fls      => fls
  | conj a b => conj (a.lift d c) (b.lift d c)
  | disj a b => disj (a.lift d c) (b.lift d c)
  | impl a b => impl (a.lift d c) (b.lift d c)
  | all a    => all (a.lift d (c + 1))
  | ex a     => ex (a.lift d (c + 1))

/-- Substitute term `s` for variable `k` (binder instantiation). -/
def subst (k : Nat) (s : DTerm) : DFormula → DFormula
  | eq t u   => eq (DTerm.subst k s t) (DTerm.subst k s u)
  | fls      => fls
  | conj a b => conj (subst k s a) (subst k s b)
  | disj a b => disj (subst k s a) (subst k s b)
  | impl a b => impl (subst k s a) (subst k s b)
  | all a    => all (subst (k + 1) (s.lift 1 0) a)
  | ex a     => ex (subst (k + 1) (s.lift 1 0) a)

/-- Quantifier-free test (used to keep the Markov posit rule honest:
MP is posited only for quantifier-free, hence decidable, matrices). -/
def isQF : DFormula → Bool
  | eq _ _   => true
  | fls      => true
  | conj a b => a.isQF && b.isQF
  | disj a b => a.isQF && b.isQF
  | impl a b => a.isQF && b.isQF
  | all _    => false
  | ex _     => false

/-- The induction-step body: `φ` with its bound variable advanced by one
distinction step, i.e. `φ[x ↦ S x]` for the de Bruijn variable 0,
leaving all other free variables fixed. -/
def stepSucc (φ : DFormula) : DFormula :=
  (φ.lift 1 1).subst 0 (DTerm.succ (DTerm.var 0))

end DFormula

end DeltaKernel
end IndisputableMonolith

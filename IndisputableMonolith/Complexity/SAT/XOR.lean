import Mathlib
import IndisputableMonolith.Complexity.SAT.CNF

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-- An XOR constraint over `n` variables: parity of a variable subset equals `parity`. -/
structure XORConstraint (n : Nat) where
  vars   : List (Var n)
  parity : Bool
deriving Repr

/-- A system of XOR constraints. -/
abbrev XORSystem (n : Nat) := List (XORConstraint n)

/-- Compute the XOR (parity) of selected variables of assignment `a`. -/
def parityOf {n} (a : Assignment n) (S : List (Var n)) : Bool :=
  S.foldl (fun acc v => Bool.xor acc (a v)) false

/-- A single XOR constraint is satisfied by `a` iff the parity matches. -/
def satisfiesXOR {n} (a : Assignment n) (c : XORConstraint n) : Prop :=
  parityOf a c.vars = c.parity

/-- An assignment satisfies an XOR system when all constraints hold. -/
def satisfiesSystem {n} (a : Assignment n) (H : XORSystem n) : Prop :=
  ∀ c ∈ H, satisfiesXOR a c

/-! ## XOR Parity Lemmas -/

/-- XOR is self-inverse: a ⊕ a = false -/
@[simp] lemma Bool.xor_self (a : Bool) : Bool.xor a a = false := by cases a <;> rfl

/-- XOR with false is identity -/
@[simp] lemma Bool.xor_false' (a : Bool) : Bool.xor a false = a := by cases a <;> rfl

/-- false XOR a = a -/
@[simp] lemma Bool.false_xor (a : Bool) : Bool.xor false a = a := by cases a <;> rfl

/-- XOR is commutative -/
lemma Bool.xor_comm (a b : Bool) : Bool.xor a b = Bool.xor b a := by cases a <;> cases b <;> rfl

/-- XOR is associative -/
lemma Bool.xor_assoc (a b c : Bool) : Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- XOR cancellation: (a ⊕ b) ⊕ b = a -/
@[simp] lemma Bool.xor_xor_cancel_right (a b : Bool) : Bool.xor (Bool.xor a b) b = a := by
  cases a <;> cases b <;> rfl

/-- Parity of empty list is false -/
@[simp] lemma parityOf_nil {n} (a : Assignment n) : parityOf a [] = false := rfl

/-- Parity of singleton is the variable value -/
@[simp] lemma parityOf_singleton {n} (a : Assignment n) (v : Var n) :
    parityOf a [v] = a v := by
  simp [parityOf, List.foldl]

/-- Helper: foldl with xor starting from init -/
lemma foldl_xor_init {n} (a : Assignment n) (init : Bool) (vs : List (Var n)) :
    vs.foldl (fun acc v => Bool.xor acc (a v)) init =
    Bool.xor init (vs.foldl (fun acc v => Bool.xor acc (a v)) false) := by
  induction vs generalizing init with
  | nil => simp
  | cons v vs ih =>
    simp only [List.foldl_cons]
    rw [ih (Bool.xor init (a v)), ih (Bool.xor false (a v))]
    simp only [Bool.false_xor]
    rw [Bool.xor_assoc]

/-- Parity of cons: XOR of head and tail parity -/
lemma parityOf_cons {n} (a : Assignment n) (v : Var n) (vs : List (Var n)) :
    parityOf a (v :: vs) = Bool.xor (a v) (parityOf a vs) := by
  unfold parityOf
  simp only [List.foldl_cons]
  rw [foldl_xor_init]
  rw [Bool.false_xor, Bool.xor_comm]

/-- If parityOf a (v :: vs) = p and parityOf a vs = q, then a v = p ⊕ q -/
lemma xor_recover_value {n} (a : Assignment n) (v : Var n) (vs : List (Var n))
    (p q : Bool) (hp : parityOf a (v :: vs) = p) (hq : parityOf a vs = q) :
    a v = Bool.xor p q := by
  rw [parityOf_cons] at hp
  -- hp: (a v) ^^ (parityOf a vs) = p
  -- hq: parityOf a vs = q
  -- Goal: a v = p ^^ q
  subst hq
  -- hp: (a v) ^^ (parityOf a vs) = p
  -- Need: a v = p ^^ (parityOf a vs)
  -- From hp: a v = (a v ^^ (parityOf a vs)) ^^ (parityOf a vs) = p ^^ (parityOf a vs)
  calc a v = Bool.xor (Bool.xor (a v) (parityOf a vs)) (parityOf a vs) := by simp
    _ = Bool.xor p (parityOf a vs) := by rw [hp]

/-- CNF "under XOR constraints": we don't rewrite into CNF; we pair them semantically. -/
structure CNFWithXOR (n : Nat) where
  φ : CNF n
  H : XORSystem n

/-- Satisfiable under XOR constraints. -/
def SatisfiableXOR {n} (ψ : CNFWithXOR n) : Prop :=
  ∃ a : Assignment n, evalCNF a ψ.φ = true ∧ satisfiesSystem a ψ.H

/-- Unique solution under XOR constraints. -/
def UniqueSolutionXOR {n} (ψ : CNFWithXOR n) : Prop :=
  ∃! a : Assignment n, evalCNF a ψ.φ = true ∧ satisfiesSystem a ψ.H

end SAT
end Complexity
end IndisputableMonolith

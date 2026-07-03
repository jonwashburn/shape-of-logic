import Mathlib

namespace IndisputableMonolith
namespace Complexity
namespace SAT

/-- Variable indices are `Fin n` for a given problem size. -/
abbrev Var (n : Nat) := Fin n

/-- Literals over `n` variables. -/
inductive Lit (n : Nat) where
  | pos (v : Var n) : Lit n
  | neg (v : Var n) : Lit n
deriving DecidableEq, Repr

/-- A clause is a disjunction of literals. -/
abbrev Clause (n : Nat) := List (Lit n)

/-- CNF: conjunction of clauses, parameterized by number of variables. -/
structure CNF (n : Nat) where
  clauses : List (Clause n)
deriving Repr

/-- Total assignments for `n` variables. -/
abbrev Assignment (n : Nat) := Var n → Bool

/-- Evaluate a literal under an assignment. -/
def evalLit {n} (a : Assignment n) : Lit n → Bool
  | .pos v => a v
  | .neg v => ! (a v)

/-- Evaluate a clause (OR over its literals). Empty clause = false. -/
def evalClause {n} (a : Assignment n) (C : Clause n) : Bool :=
  C.any (fun l => evalLit a l)

/-- Evaluate a CNF (AND over its clauses). Empty CNF = true. -/
def evalCNF {n} (a : Assignment n) (φ : CNF n) : Bool :=
  φ.clauses.all (fun C => evalClause a C)

/-- Satisfiable CNF. -/
def Satisfiable {n} (φ : CNF n) : Prop :=
  ∃ a : Assignment n, evalCNF a φ = true

/-- Uniquely satisfiable CNF. -/
def UniqueSolution {n} (φ : CNF n) : Prop :=
  ∃! (a : Assignment n), evalCNF a φ = true

end SAT
end Complexity
end IndisputableMonolith

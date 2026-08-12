import IndisputableMonolith.Loom.Grammar

/-!
# What the content means, so that "different content" is not a matter of taste

The separation theorem says two utterances lie in different gauge orbits. That is only
interesting if the two pieces of content really are different claims, and syntactic
inequality does not establish it: two formulas can differ as trees and agree as claims, and
a pair of them would be an EMBARRASSMENT rather than a witness, since the language would be
drawing a distinction the logic does not.

So content gets a semantics here, and the witness's distinctness becomes a theorem: exhibit
one finite model in which one member holds and the other fails.

The interpretation is the plainest one available. There is a single finite universe, shared
by every bound name, and a bound name is a variable rather than a sort. That choice is the
load-bearing part of this file. A two-sorted reading, where `door` ranges over the doors,
would make more pairs distinct and would be perfectly defensible as English, but it is a
stronger assumption, and a witness that needs it is a weaker witness. Measured before
choosing: 88 of the 112 pairs in the searched family that defeat a labelled-adjacency
reading remain distinct on this plainer reading, so insisting on it cost almost nothing
(`Loom/family/sorted_reading_probe.json`).

`Expr` is in negation normal form, so denial rides on the atom and there is no separate
case for it.
-/

namespace IndisputableMonolith
namespace Loom

/-- An interpretation over the universe `Fin n`: which tuples each relation holds of.
Relations are given as a predicate on the argument list, so arity is whatever the atom
brings and nothing has to be declared in advance. -/
structure Model (n : Nat) where
  holds : Nat → List (Fin n) → Bool

/-- An assignment of bound names to elements. Names not bound above an atom never reach
it, because `weave` refuses content with a free name. -/
abbrev Assign (n : Nat) := Nat → Fin n

def Assign.set {n : Nat} (env : Assign n) (name : Nat) (x : Fin n) : Assign n :=
  fun m => if m = name then x else env m

/-- Truth of content in a model, decidable because the universe is finite. -/
def evalExpr {n : Nat} (M : Model n) (env : Assign n) : Expr → Bool
  | .atom p args denied =>
      let v := M.holds p (args.map env)
      if denied then !v else v
  | .conj a b => evalExpr M env a && evalExpr M env b
  | .quant universal name body =>
      if universal then
        (List.finRange n).all fun x => evalExpr M (env.set name x) body
      else
        (List.finRange n).any fun x => evalExpr M (env.set name x) body

/-- Two pieces of content are DIFFERENT CLAIMS when some model tells them apart. This is
the property a separation witness needs, and syntactic inequality is not it. -/
def SeparatedBy {n : Nat} (M : Model n) (env : Assign n) (a b : Expr) : Prop :=
  evalExpr M env a ≠ evalExpr M env b

instance {n : Nat} (M : Model n) (env : Assign n) (a b : Expr) :
    Decidable (SeparatedBy M env a b) := by
  unfold SeparatedBy; infer_instance

end Loom
end IndisputableMonolith

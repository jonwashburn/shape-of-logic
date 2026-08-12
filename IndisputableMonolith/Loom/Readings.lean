import IndisputableMonolith.Loom.Grammar

/-!
# What a collection of local facts can see

The claim the separation witness is for is a claim about a RIVAL, so the rival has to be
defined here rather than left in a Python script. Two readings of content, both of them
the honest shape of a relational message:

* `groundBag`, a multiset of typed tuples over shared vocabulary. This is what an ingest
  contract carries: facts over declared keys, plus a count of which binders occurred. It
  has no place to put nesting, because a scope node exists only inside one claim and has
  no name the receiver already knows.
* `adjacencyBag`, strictly stronger, which also carries every parent to child label pair
  of the parse tree. This one is not really a bag, since carrying it means carrying
  anonymous per claim nodes, and it is defined anyway because a witness that only defeats
  the weaker rival should say so.

`adjacencyBag` folds denial into the atom's label, which is the FAIR version: a reading
that dropped polarity would be beaten by a triviality. Since `Expr` is already in
negation normal form, that is all denial there is.

Equality of readings is stated as `List.Perm`, which is exactly equality of the
multisets, and it is decidable, so each blindness claim in `Separation.lean` is checked by
the kernel rather than asserted.

Both readings are functions of content alone: neither ever looks at a loop. That is what
makes the separation matter rather than being an argument about encodings. A carrier that
reads content this way cannot be repaired by a better encoder downstream, because the
distinction is already gone before anything is encoded.
-/

namespace IndisputableMonolith
namespace Loom

/-- A node's label: what a local reading of the parse tree can name. -/
inductive Label where
  | root : Label
  | atom (pred : Nat) (args : List Nat) (denied : Bool) : Label
  | conj : Label
  | quant (universal : Bool) (binder : Nat) : Label
deriving DecidableEq, Repr

/-- An entry of the ground reading: a fact over shared vocabulary, or the occurrence of a
binder. Nothing here can express which binder a fact sits under. -/
inductive Ground where
  | fact (pred : Nat) (args : List Nat) (denied : Bool) : Ground
  | binder (universal : Bool) (name : Nat) : Ground
deriving DecidableEq, Repr

def labelOf : Expr → Label
  | .atom p args d => .atom p args d
  | .conj _ _ => .conj
  | .quant u b _ => .quant u b

/-- The ground reading: facts and binder occurrences, with no attachment between them. -/
def groundBag : Expr → List Ground
  | .atom p args d => [.fact p args d]
  | .conj a b => groundBag a ++ groundBag b
  | .quant u b body => .binder u b :: groundBag body

/-- The labelled adjacency reading: every parent to child edge of the parse tree, with
the root edge included so the top node is not free. -/
def adjacencyEdges : Expr → List (Label × Label)
  | .atom _ _ _ => []
  | .conj a b =>
      (Label.conj, labelOf a) :: (Label.conj, labelOf b) ::
        (adjacencyEdges a ++ adjacencyEdges b)
  | .quant u b body =>
      (Label.quant u b, labelOf body) :: adjacencyEdges body

def adjacencyBag (e : Expr) : List (Label × Label) :=
  (Label.root, labelOf e) :: adjacencyEdges e

end Loom
end IndisputableMonolith

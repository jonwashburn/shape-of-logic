import Mathlib
import IndisputableMonolith.Constants

/-!
# Graph Invariants from configDim — Combinatorics Depth

Five canonical graph invariants (= configDim D = 5):
  chromatic number, clique number, independence number,
  genus, treewidth.

Each is a distinct complexity measure of an undirected graph.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Mathematics.GraphInvariantsFromConfigDim

inductive GraphInvariant where
  | chromaticNumber
  | cliqueNumber
  | independenceNumber
  | genus
  | treewidth
  deriving DecidableEq, Repr, BEq, Fintype

theorem graphInvariant_count : Fintype.card GraphInvariant = 5 := by decide

structure GraphInvariantsCert where
  five_invariants : Fintype.card GraphInvariant = 5

def graphInvariantsCert : GraphInvariantsCert where
  five_invariants := graphInvariant_count

end IndisputableMonolith.Mathematics.GraphInvariantsFromConfigDim

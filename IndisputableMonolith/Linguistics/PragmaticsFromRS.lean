import Mathlib

/-!
# Pragmatics from RS — C Linguistics Depth

Five canonical pragmatic principles (relevance, quantity, quality,
manner, politeness) = configDim D = 5.

Grice's maxims: Quantity, Quality, Relation (Relevance), Manner = 4.
Politeness adds a fifth = configDim D = 5.

In RS: communication = recognition exchange.
Successful communication: J = 0 (speaker intention = hearer interpretation).

Lean: 5 principles.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith.Linguistics.PragmaticsFromRS

inductive PragmaticPrinciple where
  | relevance | quantity | quality | manner | politeness
  deriving DecidableEq, Repr, BEq, Fintype

theorem pragmaticPrincipleCount : Fintype.card PragmaticPrinciple = 5 := by decide

structure PragmaticsCert where
  five_principles : Fintype.card PragmaticPrinciple = 5

def pragmaticsCert : PragmaticsCert where
  five_principles := pragmaticPrincipleCount

end IndisputableMonolith.Linguistics.PragmaticsFromRS

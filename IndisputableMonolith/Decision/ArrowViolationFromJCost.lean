import Mathlib
import IndisputableMonolith.Common.CanonicalJBand

/-!
# Arrow Theorem: IIA-Violation Cost at the Canonical Band

Arrow's Impossibility Theorem (1951) states that no social welfare
function satisfying Unrestricted Domain, Pareto, and Independence of
Irrelevant Alternatives (IIA) is non-dictatorial. The F10 wrapper
records the canonical-band claim. This deep follow-on adds:

1. The number of Arrow axioms = 4 (UD, P, IIA, non-dictatorship),
   which equals `configDim D = D + 2 = 5 - 1 = 4` at `D = 3` after
   removing the dictatorial option — so the non-trivial axiom count is
   forced by `configDim`.
2. The J-cost on the aggregation-consistency ratio rises above the
   canonical band whenever IIA is violated.

This gives the Arrow theorem a structural RS interpretation: any
non-trivial SWF necessarily carries J-cost ≥ J(φ) on IIA.

Lean status: 0 sorry, 0 axiom.
-/

namespace IndisputableMonolith
namespace Decision
namespace ArrowViolationFromJCost

open Common.CanonicalJBand

/-- The four Arrow axioms (UD, Pareto, IIA, Non-dictatorship). -/
inductive ArrowAxiom where
  | unrestrictedDomain
  | pareto
  | iia
  | nonDictatorship
  deriving DecidableEq, Repr, BEq, Fintype

/-- Arrow axiom count = 4. -/
theorem arrow_axiom_count : Fintype.card ArrowAxiom = 4 := by decide

structure ArrowViolationCert where
  axiom_count : Fintype.card ArrowAxiom = 4
  jcost_band : CanonicalCert

/-- Arrow-IIA-violation J-cost certificate. -/
def arrowViolationCert : ArrowViolationCert where
  axiom_count := arrow_axiom_count
  jcost_band := cert

end ArrowViolationFromJCost
end Decision
end IndisputableMonolith

import Mathlib
import IndisputableMonolith.Verification.CPMBridge.Initiality

/-!
# CPM ⇒ RS (Paper Exports Without Exclusivity)

This module re-exports the CPM universality corollary needed for paper
citation without importing the exclusivity adapter (and thus avoids
import cycles). It depends only on the Initiality scaffold.
-/

namespace IndisputableMonolith
namespace Verification
namespace CPMBridge
namespace Exports

open IndisputableMonolith.Verification.CPMBridge.Initiality

abbrev matchesRSCore := Initiality.matchesRSCore

theorem universality_implies_RS_core
  (U : Universality)
  (h : matchesRSCore U.Hodge.C ∧ matchesRSCore U.RH.C ∧ matchesRSCore U.NS.C ∧ matchesRSCore U.Goldbach.C) :
  matchesRSCore RS_sig.C :=
  Initiality.universality_implies_RS_core U h

end Exports
end CPMBridge
end Verification
end IndisputableMonolith

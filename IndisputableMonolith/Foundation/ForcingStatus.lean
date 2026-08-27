import IndisputableMonolith.Foundation.DistinctionForcingAudit

/-!
# Forcing Status Taxonomy

This module promotes the T-1-to-T8 source classification from
`DistinctionForcingAudit` into a small reusable surface.  It intentionally does
not re-invent the taxonomy: downstream capstones should cite the same
`ChainLink`, `LinkSource`, `linkSource`, and `LinkSourceAudit` declarations.
-/

namespace IndisputableMonolith
namespace Foundation
namespace ForcingStatus

abbrev ChainLink := DistinctionForcingAudit.ChainLink
abbrev LinkSource := DistinctionForcingAudit.LinkSource
abbrev LinkSourceAudit := DistinctionForcingAudit.LinkSourceAudit

/-- The canonical source classification for each T-1-to-T8 link. -/
def linkSource : ChainLink → LinkSource :=
  DistinctionForcingAudit.linkSource

/-- The source classification already proved in `DistinctionForcingAudit`. -/
theorem linkSourceAudit_holds : LinkSourceAudit :=
  DistinctionForcingAudit.linkSourceAudit_holds

/-- Bridge-obstruction bookkeeping.  `proved` means there is a real
countermodel/independence theorem.  `documentedBridgeDefinition` means the
bridge is an interpretation encoded by definition and explicitly marked as
such.  `open` means the obstruction is a named formalization target, not a
proved claim. -/
inductive BridgeObstructionStatus where
  | proved
  | documentedBridgeDefinition
  | open
  deriving DecidableEq

/-- A status-only bridge entry.  This is deliberately not a proof of
independence; proof-bearing modules attach the actual theorem next to entries
whose status is `proved`. -/
structure BridgeStatusEntry where
  name : String
  status : BridgeObstructionStatus

end ForcingStatus
end Foundation
end IndisputableMonolith
